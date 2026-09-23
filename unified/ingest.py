from __future__ import annotations

import asyncio
import io
import logging

from aiogram import Bot
from aiogram.types import Message

from unified.parser import extract_name
from unified.store import save_character
from services.hash_service import hash_photo, hash_video
from services.source_resolver import resolve_source_collection, output_command_from_message
from unified.source_whitelist import is_allowed_source, forwarded_origin_chat

log = logging.getLogger(__name__)


def _media(target: Message):
    for attr, media_type in (("photo", "photo"), ("video", "video"), ("animation", "video")):
        obj = getattr(target, attr, None)
        if obj:
            return obj, media_type

    obj = getattr(target, "document", None)
    if obj:
        mime = str(getattr(obj, "mime_type", "") or "").lower()
        filename = str(getattr(obj, "file_name", "") or "").lower()
        if mime.startswith("image/") or filename.endswith((".jpg", ".jpeg", ".png", ".webp", ".gif")):
            return obj, "photo"
        if mime.startswith("video/") or filename.endswith((".mp4", ".mkv", ".mov", ".webm")):
            return obj, "video"

    return None, None


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


async def ingest_message(bot: Bot, message: Message, trusted_user_ids: set[int] | None = None) -> bool:
    # The only accepted Adding input is the message itself forwarded from an
    # explicitly configured source channel. A reply-to message is never used
    # as an authorization shortcut.
    target = message
    trusted = bool(
        trusted_user_ids
        and getattr(getattr(target, "from_user", None), "id", None) in trusted_user_ids
    )
    if not _forwarded(target) and not trusted:
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

    media, media_type = _media(target)
    if not media:
        return False

    # After authorization, resolve the canonical source collection. Content
    # parsing can classify the source, but it cannot authorize ingestion.
    source_key = resolve_source_collection(target)
    if not source_key:
        log.warning(
            "SKIP unknown forwarded source chat=%s message=%s",
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
    if not name:
        log.warning(
            "SKIP source=%s: character name not parsed message=%s",
            source_key,
            getattr(target, "message_id", None),
        )
        return False

    command = output_command_from_message(target, source_key) or "/name"

    try:
        data = await _download(bot, str(getattr(media, "file_id", "") or ""))
        if not data:
            return False

        hashed = await asyncio.to_thread(
            hash_photo if media_type == "photo" else hash_video,
            data,
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

        await save_character(
            name=name,
            command=command,
            source_key=source_key,
            media_type=media_type,
            file_unique_id=str(getattr(media, "file_unique_id", "") or ""),
            media_hash=hashed,
            source_origin=origin,
            archive=(message.chat.id, message.message_id),
        )
        return True
    except Exception:
        log.exception("forward-only ingest failed")
        return False
