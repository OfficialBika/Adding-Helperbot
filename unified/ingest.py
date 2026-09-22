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
        if mime.startswith("image/") or filename.endswith((".jpg",".jpeg",".png",".webp",".gif")):
            return obj, "photo"
        if mime.startswith("video/") or filename.endswith((".mp4",".mkv",".mov",".webm")):
            return obj, "video"
    return None, None

async def ingest_message(bot: Bot, message: Message) -> bool:
    target = message.reply_to_message or message
    name = extract_name(getattr(target, "caption", None) or getattr(target, "text", None))
    media, media_type = _media(target)
    if not name or not media:
        return False

    source_key = resolve_source_collection(target)
    origin_obj = getattr(target, "forward_origin", None)
    origin_chat = getattr(origin_obj, "chat", None) or getattr(origin_obj, "sender_chat", None)
    origin_mid = getattr(origin_obj, "message_id", None)

    # Do not turn arbitrary user uploads in the Adding group into database records.
    if not source_key and not (origin_chat and origin_mid is not None):
        return False
    source_key = source_key or "unknown"

    command = output_command_from_message(target, None) or "/name"

    try:
        result = await asyncio.wait_for(
            bot.download(getattr(media, "file_id", "")),
            timeout=30,
        )
        if isinstance(result, io.BytesIO):
            data = result.getvalue()
        elif hasattr(result, "read"):
            data = result.read()
        else:
            return False

        hashed = await asyncio.to_thread(
            hash_photo if media_type == "photo" else hash_video,
            data,
        )

        origin = None
        if origin_chat and origin_mid is not None:
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
        log.exception("unified ingest failed")
        return False
