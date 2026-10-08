from __future__ import annotations

import logging

from aiogram import Bot
from aiogram.types import Message

from unified.parser import parse_message
from unified.source_resolver import (
    BOT_SOURCE_COLLECTION,
    BOT_SOURCE_USER_ID,
    grabber_source_variant,
    output_command_from_message,
    resolve_source_collection,
    resolve_trusted_inline_collection,
    source_origin_key,
)
from unified.source_whitelist import forwarded_origin_chat, is_allowed_source
from unified.store import save_character

log = logging.getLogger("unified-ingest")


def _media_info(target: Message) -> dict | None:
    photos = getattr(target, "photo", None) or []
    photo_sizes = [p for p in photos if getattr(p, "file_id", None)]
    if photo_sizes:
        selected = max(
            photo_sizes,
            key=lambda p: (
                int(getattr(p, "width", 0) or 0) * int(getattr(p, "height", 0) or 0),
                int(getattr(p, "file_size", 0) or 0),
            ),
        )
        return {
            "media_type": "photo",
            "file_id": str(getattr(selected, "file_id", "") or ""),
            "file_unique_id": str(getattr(selected, "file_unique_id", "") or ""),
            "file_ids": [str(getattr(p, "file_id", "") or "") for p in photo_sizes if getattr(p, "file_id", None)],
            "file_unique_ids": [str(getattr(p, "file_unique_id", "") or "") for p in photo_sizes if getattr(p, "file_unique_id", None)],
            "width": int(getattr(selected, "width", 0) or 0),
            "height": int(getattr(selected, "height", 0) or 0),
            "duration": 0,
            "file_size": int(getattr(selected, "file_size", 0) or 0),
            "mime_type": "image/jpeg",
            "file_name": "",
        }

    for attr, media_type in (("video", "video"), ("animation", "video")):
        obj = getattr(target, attr, None)
        if obj is not None and getattr(obj, "file_id", None):
            return {
                "media_type": media_type,
                "file_id": str(getattr(obj, "file_id", "") or ""),
                "file_unique_id": str(getattr(obj, "file_unique_id", "") or ""),
                "file_ids": [str(getattr(obj, "file_id", "") or "")],
                "file_unique_ids": [str(getattr(obj, "file_unique_id", "") or "")],
                "width": int(getattr(obj, "width", 0) or 0),
                "height": int(getattr(obj, "height", 0) or 0),
                "duration": int(getattr(obj, "duration", 0) or 0),
                "file_size": int(getattr(obj, "file_size", 0) or 0),
                "mime_type": str(getattr(obj, "mime_type", "") or ""),
                "file_name": "",
            }

    obj = getattr(target, "document", None)
    if obj is not None and getattr(obj, "file_id", None):
        mime = str(getattr(obj, "mime_type", "") or "").lower()
        filename = str(getattr(obj, "file_name", "") or "").lower()
        if mime.startswith("image/") or filename.endswith((".jpg", ".jpeg", ".png", ".webp", ".gif")):
            media_type = "photo"
        elif mime.startswith("video/") or filename.endswith((".mp4", ".mkv", ".mov", ".webm")):
            media_type = "video"
        else:
            return None
        return {
            "media_type": media_type,
            "file_id": str(getattr(obj, "file_id", "") or ""),
            "file_unique_id": str(getattr(obj, "file_unique_id", "") or ""),
            "file_ids": [str(getattr(obj, "file_id", "") or "")],
            "file_unique_ids": [str(getattr(obj, "file_unique_id", "") or "")],
            "width": int(getattr(obj, "width", 0) or 0),
            "height": int(getattr(obj, "height", 0) or 0),
            "duration": int(getattr(obj, "duration", 0) or 0),
            "file_size": int(getattr(obj, "file_size", 0) or 0),
            "mime_type": mime,
            "file_name": str(getattr(obj, "file_name", "") or ""),
        }
    return None


def _is_forwarded(target: Message) -> bool:
    return bool(
        getattr(target, "forward_origin", None)
        or getattr(target, "forward_from_chat", None)
        or getattr(target, "forward_from", None)
        or getattr(target, "forward_sender_name", None)
    )


def _configured_bot_sender(target: Message) -> bool:
    user = getattr(target, "from_user", None)
    if user is None or not getattr(user, "is_bot", False):
        return False
    username = str(getattr(user, "username", "") or "").strip().lower()
    if username and f"@{username.lstrip('@')}" in BOT_SOURCE_COLLECTION:
        return True
    try:
        return int(getattr(user, "id", 0) or 0) in BOT_SOURCE_USER_ID
    except Exception:
        return False


async def ingest_message(
    bot: Bot,
    message: Message,
    trusted_user_ids: set[int] | None = None,
    trusted_source_collection: str | None = None,
) -> dict | bool:
    target = message
    from_user = getattr(target, "from_user", None)
    sender_id = getattr(from_user, "id", None)
    trusted = bool(
        (trusted_user_ids and sender_id in trusted_user_ids)
        or _configured_bot_sender(target)
    )
    forwarded = _is_forwarded(target)

    if not forwarded and not trusted:
        log.info(
            "ADD skip untrusted message=%s from_user=%s",
            getattr(target, "message_id", None),
            sender_id,
        )
        return False

    if forwarded and not trusted and not is_allowed_source(target):
        origin = forwarded_origin_chat(target)
        log.warning(
            "ADD skip unauthorized source message=%s chat=%s username=%s",
            getattr(target, "message_id", None),
            getattr(origin, "id", None),
            getattr(origin, "username", None),
        )
        return False

    source_key = trusted_source_collection or resolve_source_collection(target)
    if not source_key and trusted:
        source_key = resolve_trusted_inline_collection(target)
    if not source_key:
        return False

    media_info = _media_info(target)
    media_type = media_info["media_type"] if media_info else "metadata"
    text = "\n".join(
        value
        for value in (
            getattr(target, "caption", None),
            getattr(target, "text", None),
            getattr(target, "html_text", None),
            getattr(target, "md_text", None),
        )
        if isinstance(value, str) and value.strip()
    )

    parsed = parse_message(text, source_key=source_key)
    if not parsed:
        log.info(
            "ADD parser no-match source=%s message=%s",
            source_key,
            getattr(target, "message_id", None),
        )
        return False

    name = parsed.name
    character_id = parsed.character_id
    command = output_command_from_message(target, source_key) or "/name"
    source_variant = grabber_source_variant(target) if source_key == "items_grabber_fw" else None
    source_origin = source_origin_key(target)

    if media_info and not str(media_info.get("file_unique_id") or "").strip():
        return {
            "status": "skipped",
            "document": None,
            "reason": "missing_file_unique_id",
        }

    media_meta = {
        "width": media_info["width"] if media_info else 0,
        "height": media_info["height"] if media_info else 0,
        "duration": media_info["duration"] if media_info else 0,
        "file_size": media_info["file_size"] if media_info else 0,
        "mime_type": media_info["mime_type"] if media_info else "",
        "file_name": media_info["file_name"] if media_info else "",
    }

    saved = await save_character(
        name=name,
        character_id=character_id,
        command=command,
        source_key=source_key,
        media_type=media_type,
        file_unique_id=media_info["file_unique_id"] if media_info else None,
        file_id=media_info["file_id"] if media_info else None,
        file_unique_ids=media_info["file_unique_ids"] if media_info else [],
        file_ids=media_info["file_ids"] if media_info else [],
        media_meta=media_meta,
        source_origin=source_origin,
        source_variant=source_variant,
        source_signature=next(
            (
                str(getattr(obj, "author_signature", "") or "").strip()
                for obj in (getattr(target, "forward_origin", None), target)
                if str(getattr(obj, "author_signature", "") or "").strip()
            ),
            None,
        ),
        archive=(
            int(getattr(target.chat, "id")),
            int(getattr(target, "message_id")),
        ),
    )
    log.info(
        "ADD saved source=%s parser=%s confidence=%.3f message=%s name=%s id=%s status=%s",
        source_key,
        parsed.parser,
        parsed.confidence,
        getattr(target, "message_id", None),
        name,
        character_id,
        saved.get("status") if isinstance(saved, dict) else "unknown",
    )
    return saved
