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


def _telegram_uids(message: Message, media_type: str, media_obj) -> list[str]:
    """Return every native Telegram UID exposed by the current media object.

    For photos Telegram exposes several PhotoSize objects; every size is a
    legitimate exact UID and must be checked. For other media the media object
    itself is the exact identity.
    """
    values: list[str] = []
    if media_type == "photo":
        for photo in (getattr(message, "photo", None) or []):
            uid = str(getattr(photo, "file_unique_id", "") or "").strip()
            if uid and uid not in values:
                values.append(uid)
    uid = str(getattr(media_obj, "file_unique_id", "") or "").strip()
    if uid and uid not in values:
        values.append(uid)
    return values


def _uid_query_new(uids: list[str]) -> dict:
    # New unified records always merge all Telegram PhotoSize/media UIDs here.
    return {"file_unique_ids": {"$in": uids}}


def _uid_query_legacy(uids: list[str]) -> dict:
    # Compatibility for old/imported records. Exact Telegram UID only.
    return {
        "$or": [
            {"telegram_file_unique_id": {"$in": uids}},
            {"file_unique_id": {"$in": uids}},
            {"photo_file_unique_id": {"$in": uids}},
            {"video_file_unique_id": {"$in": uids}},
            {"media.file_unique_id": {"$in": uids}},
        ]
    }


async def _exact_find(scope: list[str] | None, uids: list[str]):
    """Use the canonical multikey UID index first, then legacy UID fields."""
    if not uids:
        return None
    prefix = {"source_key": {"$in": scope}} if scope else {}
    doc = await characters.find_one({**prefix, **_uid_query_new(uids)})
    if doc:
        return doc
    return await characters.find_one({**prefix, **_uid_query_legacy(uids)})


async def _exact_global_candidates(uids: list[str], limit: int = 2) -> list[dict]:
    if not uids:
        return []
    docs = await characters.find(
        _uid_query_new(uids),
        {
            "_id": 1,
            "name": 1,
            "command": 1,
            "source_key": 1,
            "file_unique_ids": 1,
            "telegram_file_unique_id": 1,
        },
    ).limit(limit).to_list(length=limit)
    if docs:
        return docs
    return await characters.find(
        _uid_query_legacy(uids),
        {
            "_id": 1,
            "name": 1,
            "command": 1,
            "source_key": 1,
            "file_unique_ids": 1,
            "telegram_file_unique_id": 1,
        },
    ).limit(limit).to_list(length=limit)


async def lookup_message(bot: Bot, message: Message, *, allow_global_fallback: bool = False):
    """Exact Telegram file_unique_id lookup.

    Auto lookup is source-scoped. Manual lookup may perform a global exact-UID
    recovery only after the source-scoped exact lookup fails. No filename,
    message-id, SHA, pHash, or visual-similarity fallback is used.
    """
    media = extract_media(message)
    if not media:
        return None, "no_media"

    source_message = media.source_message
    collections = _scope(source_message)
    if not collections and not allow_global_fallback:
        return None, "source_unknown"

    uids = _telegram_uids(source_message, media.media_type, media.obj)
    if not uids:
        return None, "no_file_unique_id"

    log.info(
        "UID DEBUG message=%s source_message=%s media_type=%s collections=%s uids=%s",
        getattr(message, "message_id", None),
        getattr(source_message, "message_id", None),
        media.media_type,
        collections,
        uids,
    )

    if collections:
        doc = await _exact_find(collections, uids)
        if doc:
            log.info(
                "UID DEBUG source_match message=%s source=%s name=%s",
                getattr(message, "message_id", None),
                doc.get("source_key"),
                doc.get("name"),
            )
            return doc, "uid"

        # Diagnostic-only global probe. It never changes auto lookup behavior.
        probe = (await _exact_global_candidates(uids, limit=1) or [None])[0]
        if probe:
            log.warning(
                "UID DEBUG cross_source_match message=%s requested_sources=%s db_source=%s name=%s",
                getattr(message, "message_id", None),
                collections,
                probe.get("source_key"),
                probe.get("name"),
            )
        else:
            log.warning(
                "UID DEBUG database_uid_miss message=%s requested_sources=%s",
                getattr(message, "message_id", None),
                collections,
            )

    if not allow_global_fallback:
        return None, "not_found_uid"

    global_docs = await _exact_global_candidates(uids, limit=2)
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
