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


async def ingest_message(bot: Bot, message: Message) -> bool:
    # The only accepted Adding input is a forwarded channel/source post.
    target = message.reply_to_message or message
    if not _forwarded(target):
        return False

    media, media_type = _media(target)
    if not media:
        return False

    # Source must be identified from Telegram forward metadata or the known
    # source-content rules. Unknown sources are not silently stored.
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
