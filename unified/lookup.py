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


def _uid_query(uids: list[str]) -> dict:
    # Exact Telegram file_unique_id only. Supports the new unified schema plus
    # legacy UID field names; never falls back to hashes or message IDs.
    return {
        "$or": [
            {"file_unique_ids": {"$in": uids}},
            {"telegram_file_unique_id": {"$in": uids}},
            {"file_unique_id": {"$in": uids}},
            {"photo_file_unique_id": {"$in": uids}},
            {"video_file_unique_id": {"$in": uids}},
            {"media.file_unique_id": {"$in": uids}},
        ]
    }


async def lookup_message(bot: Bot, message: Message, *, allow_global_fallback: bool = False):
    """Exact Telegram file_unique_id lookup only.

    No SHA-256, pHash, video similarity, filename, message-id, or download
    fallback is used. Auto lookup is source-scoped; an unknown source is a miss.
    """
    media = extract_media(message)
    if not media:
        return None, "no_media"

    source_message = media.source_message
    collections = _scope(source_message)
    if not collections and not allow_global_fallback:
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
    if collections:
        query = {
            "source_key": {"$in": collections},
            **_uid_query(uids),
        }
        doc = await characters.find_one(query)
        if doc:
            return doc, "uid"

    # Manual lookup may recover globally after the source-scoped exact match
    # fails. Auto lookup stays strictly source-scoped.
    if not allow_global_fallback:
        return None, "not_found_uid"

    # Global recovery remains exact UID only and ambiguity-safe.
    global_query = _uid_query(uids)
    global_docs = await characters.find(
        global_query,
        {
            "_id": 1,
            "name": 1,
            "command": 1,
            "source_key": 1,
            "file_unique_ids": 1,
            "telegram_file_unique_id": 1,
        },
    ).limit(2).to_list(length=2)

    if len(global_docs) == 1:
        return global_docs[0], "uid_global_recovery"

    if len(global_docs) > 1:
        log.warning(
            "UID global recovery ambiguous message=%s source=%s candidates=%s",
            getattr(message, "message_id", None),
            collections,
            len(global_docs),
        )
        return None, "ambiguous_global_uid"

    return None, "not_found_uid"
