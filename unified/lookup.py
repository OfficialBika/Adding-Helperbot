from __future__ import annotations

import logging

from aiogram import Bot
from aiogram.types import Message

from services.source_resolver import resolve_lookup_scope
from utils.media import extract_media
from unified.store import characters

log = logging.getLogger(__name__)


def _scope(message: Message) -> list[str]:
    try:
        scope = resolve_lookup_scope(message)
        return [str(x).strip().lower() for x in (scope.collections or []) if str(x).strip()]
    except Exception as exc:
        log.info("source scope unavailable: %s", exc)
        return []


def _photo_uids(source_message: Message) -> list[str]:
    values: list[str] = []
    for photo in (getattr(source_message, "photo", None) or []):
        uid = str(getattr(photo, "file_unique_id", "") or "").strip()
        if uid and uid not in values:
            values.append(uid)
    return values


async def lookup_message(bot: Bot, message: Message):
    """Exact Telegram file_unique_id lookup only.

    No SHA-256, pHash, video similarity, filename, message-id, or download
    fallback is used. Auto lookup is source-scoped; an unknown source is a miss.
    """
    media = extract_media(message)
    if not media:
        return None, "no_media"

    source_message = media.source_message
    collections = _scope(source_message)
    if not collections:
        return None, "source_unknown"

    uids = _photo_uids(source_message) if media.media_type == "photo" else []
    uid = str(getattr(media.obj, "file_unique_id", "") or "").strip()
    if uid and uid not in uids:
        uids.append(uid)

    if not uids:
        return None, "no_file_unique_id"

    # Query only Telegram native file_unique_id values. Mongo multikey indexes
    # on file_unique_ids and the scalar legacy field keep this exact fallback
    # fast without downloading media.
    query = {
        "source_key": {"$in": collections},
        "$or": [
            {"file_unique_ids": {"$in": uids}},
            {"telegram_file_unique_id": {"$in": uids}},
        ],
    }
    doc = await characters.find_one(query)
    if doc:
        return doc, "uid"

    return None, "not_found_source_uid"
