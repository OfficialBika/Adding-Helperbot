from __future__ import annotations

import asyncio
import io
import logging

from aiogram import Bot
from aiogram.types import Message

from unified.parser import extract_name, extract_character_id
from unified.store import save_character
from services.hash_service import hash_photo, hash_video
from services.source_resolver import resolve_source_collection, resolve_trusted_inline_collection, output_command_from_message
from unified.source_whitelist import is_allowed_source, forwarded_origin_chat

log = logging.getLogger(__name__)


def _media_info(target: Message) -> dict | None:
    """Extract the actual Telegram media object and all stable media identifiers.

    aiogram represents Message.photo as a list[PhotoSize]. Returning that list
    directly was the cause of the previous file_id=None/empty-download failure.
    We keep every PhotoSize file_id/file_unique_id and download from the largest
    available PhotoSize.
    """
    photos = getattr(target, "photo", None) or []
    if photos:
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
                "media": selected,
                "media_type": "photo",
                "file_id": str(getattr(selected, "file_id", "") or ""),
                "file_unique_id": str(getattr(selected, "file_unique_id", "") or ""),
                "file_ids": [
                    str(getattr(p, "file_id", "") or "")
                    for p in photo_sizes
                    if getattr(p, "file_id", None)
                ],
                "file_unique_ids": [
                    str(getattr(p, "file_unique_id", "") or "")
                    for p in photo_sizes
                    if getattr(p, "file_unique_id", None)
                ],
                "width": int(getattr(selected, "width", 0) or 0),
                "height": int(getattr(selected, "height", 0) or 0),
                "duration": 0,
                "file_size": int(getattr(selected, "file_size", 0) or 0),
                "mime_type": "image/jpeg",
                "file_name": "",
            }

    for attr, media_type in (("video", "video"), ("animation", "video")):
        obj = getattr(target, attr, None)
        if obj and getattr(obj, "file_id", None):
            return {
                "media": obj,
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
                "file_name": str(getattr(obj, "file_name", "") or ""),
            }

    obj = getattr(target, "document", None)
    if obj and getattr(obj, "file_id", None):
        mime = str(getattr(obj, "mime_type", "") or "").lower()
        filename = str(getattr(obj, "file_name", "") or "").lower()
        if mime.startswith("image/") or filename.endswith((".jpg", ".jpeg", ".png", ".webp", ".gif")):
            media_type = "photo"
        elif mime.startswith("video/") or filename.endswith((".mp4", ".mkv", ".mov", ".webm")):
            media_type = "video"
        else:
            return None
        return {
            "media": obj,
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
            "file_name": str(getattr(obj, "file_name", "") or ""),
        }

    return None


def _forwarded(target: Message) -> bool:
    return bool(
        getattr(target, "forward_origin", None)
        or getattr(target, "forward_from_chat", None)
        or getattr(target, "forward_from", None)
        or getattr(target, "forward_sender_name", None)
    )


async def _download(bot: Bot, file_id: str) -> bytes | None:
    if not file_id:
        return None
    result = await asyncio.wait_for(bot.download(file_id), timeout=45)
    if isinstance(result, io.BytesIO):
        return result.getvalue()
    if hasattr(result, "read"):
        value = result.read()
        return value if isinstance(value, bytes) else None
    return None


async def ingest_message(
    bot: Bot,
    message: Message,
    trusted_user_ids: set[int] | None = None,
    trusted_source_collection: str | None = None,
) -> bool:
    # The only accepted Adding input is the message itself forwarded from an
    # explicitly configured source channel. A reply-to message is never used
    # as an authorization shortcut.
    target = message
    trusted = bool(
        trusted_user_ids
        and getattr(getattr(target, "from_user", None), "id", None) in trusted_user_ids
    )
    if not _forwarded(target) and not trusted:
        log.info(
            "SKIP untrusted message chat=%s message=%s from_user=%s",
            getattr(getattr(target, "chat", None), "id", None),
            getattr(target, "message_id", None),
            getattr(getattr(target, "from_user", None), "id", None),
        )
        return False

    if not trusted and not is_allowed_source(target):
        origin_chat = forwarded_origin_chat(target)
        log.warning(
            "SKIP unauthorized forwarded source chat=%s username=%s message=%s",
            getattr(origin_chat, "id", None),
            getattr(origin_chat, "username", None),
            getattr(target, "message_id", None),
        )
        return False

    media_info = _media_info(target)
    if not media_info:
        log.warning(
            "SKIP no supported media chat=%s message=%s",
            getattr(getattr(target, "chat", None), "id", None),
            getattr(target, "message_id", None),
        )
        return False

    media = media_info["media"]
    media_type = media_info["media_type"]

    # After authorization, resolve the canonical source collection. Content
    # parsing can classify the source, but it cannot authorize ingestion.
    source_key = trusted_source_collection or resolve_source_collection(target)
    if not source_key and trusted:
        source_key = resolve_trusted_inline_collection(target)
    if not source_key:
        log.warning(
            "SKIP unknown source chat=%s message=%s",
            getattr(getattr(target, "chat", None), "id", None),
            getattr(target, "message_id", None),
        )
        return False

    text = "\n".join(
        x for x in (
            getattr(target, "caption", None),
            getattr(target, "text", None),
            getattr(target, "html_text", None),
            getattr(target, "md_text", None),
        ) if isinstance(x, str) and x.strip()
    )

    name = extract_name(text)
    character_id = extract_character_id(text)
    if not name:
        log.warning(
            "SKIP source=%s: character name not parsed message=%s",
            source_key,
            getattr(target, "message_id", None),
        )
        return False

    command = output_command_from_message(target, source_key) or "/name"

    try:
        file_id = media_info["file_id"]
        data = None
        try:
            data = await _download(bot, file_id)
        except Exception as exc:
            # Metadata/file IDs are still valid even when Bot API download is
            # unavailable (for example a file over the current download limit).
            log.warning(
                "MEDIA download failed source=%s message=%s type=%s size=%s error=%s",
                source_key,
                getattr(target, "message_id", None),
                media_type,
                media_info.get("file_size", 0),
                exc,
            )

        hashed = None
        if data:
            log.info(
                "INGEST media ready source=%s message=%s type=%s bytes=%s name=%s id=%s",
                source_key,
                getattr(target, "message_id", None),
                media_type,
                len(data),
                name,
                character_id,
            )
            hashed = await asyncio.to_thread(
                hash_photo if media_type == "photo" else hash_video,
                data,
            )
        else:
            log.warning(
                "INGEST metadata-only save source=%s message=%s type=%s file_id_present=%s unique_ids=%s",
                source_key,
                getattr(target, "message_id", None),
                media_type,
                bool(file_id),
                len(media_info.get("file_unique_ids", [])),
            )

        origin_obj = getattr(target, "forward_origin", None)
        origin_chat = getattr(origin_obj, "chat", None) or getattr(origin_obj, "sender_chat", None)
        origin_mid = getattr(origin_obj, "message_id", None)

        if origin_chat is None:
            origin_chat = getattr(target, "forward_from_chat", None)
            origin_mid = origin_mid or getattr(target, "forward_from_message_id", None)

        origin = None
        if origin_chat is not None and origin_mid is not None:
            origin = (int(origin_chat.id), int(origin_mid))

        saved = await save_character(
            name=name,
            character_id=character_id,
            command=command,
            source_key=source_key,
            media_type=media_type,
            file_id=file_id,
            file_ids=media_info["file_ids"],
            file_unique_id=media_info["file_unique_id"],
            file_unique_ids=media_info["file_unique_ids"],
            media_meta={
                "width": media_info["width"],
                "height": media_info["height"],
                "duration": media_info["duration"],
                "file_size": media_info["file_size"],
                "mime_type": media_info["mime_type"],
                "file_name": media_info["file_name"],
            },
            media_hash=hashed,
            source_origin=origin,
            archive=(message.chat.id, message.message_id),
        )
        log.info(
            "INGEST save completed source=%s message=%s name=%s id=%s status=%s",
            source_key,
            getattr(target, "message_id", None),
            name,
            character_id,
            saved.get("status") if isinstance(saved, dict) else "unknown",
        )
        return True
    except Exception:
        log.exception("forward-only ingest failed")
        return False
