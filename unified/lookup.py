from __future__ import annotations

import asyncio
import io
import logging
from typing import Any

from aiogram import Bot
from aiogram.types import Message

from services.hash_service import hamming_hex, hash_photo, hash_video
from services.source_resolver import resolve_lookup_scope, source_origin_key
from unified.config import settings
from unified.store import characters
from unified.lookup_index import lookup_index
from utils.media import extract_media

log = logging.getLogger(__name__)

# Hash fallback is deliberately behind exact Telegram UID lookup.
# It downloads only when UID lookup has failed, and never replaces UID identity.
_HASH_DOWNLOAD_SEM = asyncio.Semaphore(3)
_HASH_CANDIDATE_LIMIT = 1200
_PHASH_THRESHOLD = 8
_PHASH_MIN_SCORE = 0.84
_PHASH_MIN_MARGIN = 0.035


def _scope(message: Message) -> list[str]:
    try:
        scope = resolve_lookup_scope(message)
        return [str(x).strip().lower() for x in (scope.collections or []) if str(x).strip()]
    except Exception as exc:
        log.info("source scope unavailable: %s", exc)
        return []


def _telegram_uids(message: Message, media_type: str, media_obj) -> list[str]:
    """Return every native Telegram UID exposed by the current media object."""
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




def _ram_exact_find(uids: list[str], collections: list[str]) -> dict | None:
    for source in collections:
        for uid in uids:
            doc = lookup_index.ram.get(uid, source)
            if doc:
                return doc
    return None


def _select_global_candidate(candidates: list[dict]) -> dict | None:
    if len(candidates) == 1:
        return candidates[0]
    if len(candidates) > 1:
        catch_matches = [
            doc for doc in candidates
            if str(doc.get("source_key") or "").strip().lower()
            == "items_character_catcher"
        ]
        if len(catch_matches) == 1:
            return catch_matches[0]
    return None


def _uid_query_new(uids: list[str]) -> dict:
    return {"file_unique_ids": {"$in": uids}}


def _uid_query_legacy(uids: list[str]) -> dict:
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
    if not uids:
        return None
    prefix = {"source_key": {"$in": scope}} if scope else {}
    doc = await characters.find_one({**prefix, **_uid_query_new(uids)})
    if doc:
        return doc
    return await characters.find_one({**prefix, **_uid_query_legacy(uids)})




async def _bot_message_origin_fallback(scope: list[str] | None, message: Message):
    """Recover direct bot-to-bot media using the source message id.

    Bot-to-bot delivery can have no forward_origin at all. When the same source
    message was previously archived with source_origin, a unique source-scoped
    message-id match is safe enough to use as a final exact recovery path.
    """
    from_user = getattr(message, "from_user", None)
    if not getattr(from_user, "is_bot", False):
        return None

    message_id = getattr(message, "message_id", None)
    if message_id is None:
        return None

    prefix = {"source_key": {"$in": scope}} if scope else {}
    query = {
        **prefix,
        "source_origin.message_id": int(message_id),
    }
    projection = {
        "_id": 1,
        "name": 1,
        "command": 1,
        "source_key": 1,
        "file_unique_ids": 1,
        "telegram_file_unique_id": 1,
        "source_origin": 1,
    }
    docs = await characters.find(query, projection).limit(2).to_list(length=2)
    if len(docs) == 1:
        return docs[0]
    if len(docs) > 1:
        log.warning(
            "BOT SOURCE MESSAGE ambiguous message=%s sources=%s",
            message_id,
            [doc.get("source_key") for doc in docs],
        )
    return None


async def _origin_exact_find(scope: list[str] | None, message: Message):
    """Recover records from the original forwarded source message identity.

    Some older records may have a valid source-origin record but lack the
    currently presented Telegram file_unique_id (for example after a historical
    Telegram file_unique_id migration). This fallback is still source-scoped
    and only accepts a unique source-origin match.
    """
    origin = source_origin_key(message)
    if not origin:
        return None

    chat_id, message_id = origin
    prefix = {"source_key": {"$in": scope}} if scope else {}
    query = {
        **prefix,
        "source_origin.chat_id": int(chat_id),
        "source_origin.message_id": int(message_id),
    }
    projection = {
        "_id": 1,
        "name": 1,
        "command": 1,
        "source_key": 1,
        "file_unique_ids": 1,
        "telegram_file_unique_id": 1,
        "source_origin": 1,
    }
    docs = await characters.find(query, projection).limit(2).to_list(length=2)
    if len(docs) == 1:
        return docs[0]
    if len(docs) > 1:
        log.warning(
            "SOURCE ORIGIN ambiguous chat=%s message=%s sources=%s",
            chat_id,
            message_id,
            [doc.get("source_key") for doc in docs],
        )
    return None


async def _exact_global_candidates(uids: list[str], limit: int = 2) -> list[dict]:
    if not uids:
        return []
    projection = {
        "_id": 1,
        "name": 1,
        "command": 1,
        "source_key": 1,
        "file_unique_ids": 1,
        "telegram_file_unique_id": 1,
    }
    docs = await characters.find(_uid_query_new(uids), projection).limit(limit).to_list(length=limit)
    if docs:
        return docs
    return await characters.find(_uid_query_legacy(uids), projection).limit(limit).to_list(length=limit)


def _sha_query(sha: str) -> dict:
    return {
        "$or": [
            {"sha256": sha},
            {"sha256_aliases": sha},
        ]
    }



async def _video_signature_find(scope: list[str] | None, signature: str):
    if not signature:
        return None
    prefix = {"source_key": {"$in": scope}} if scope else {}
    projection = {
        "_id": 1,
        "name": 1,
        "command": 1,
        "source_key": 1,
        "video_signature": 1,
        "media_type": 1,
    }
    return await characters.find_one(
        {**prefix, "video_signature": signature},
        projection,
    )


async def _video_signature_global_candidates(signature: str, limit: int = 2) -> list[dict]:
    if not signature:
        return []
    projection = {
        "_id": 1,
        "name": 1,
        "command": 1,
        "source_key": 1,
        "video_signature": 1,
        "media_type": 1,
    }
    return await characters.find(
        {"video_signature": signature},
        projection,
    ).limit(limit).to_list(length=limit)


async def _hash_exact_find(scope: list[str] | None, sha: str):
    if not sha:
        return None
    prefix = {"source_key": {"$in": scope}} if scope else {}
    return await characters.find_one({**prefix, **_sha_query(sha)})


async def _hash_global_candidates(sha: str, limit: int = 2) -> list[dict]:
    if not sha:
        return []
    projection = {
        "_id": 1,
        "name": 1,
        "command": 1,
        "source_key": 1,
        "sha256": 1,
        "sha256_aliases": 1,
    }
    return await characters.find(_sha_query(sha), projection).limit(limit).to_list(length=limit)


def _chunks(value: str | None, count: int = 9) -> list[str]:
    if not value:
        return []
    try:
        text = str(value).strip().lower()
        number = int(text, 16)
    except Exception:
        return []
    bits = len(str(value).strip()) * 4
    if bits <= 0 or count > bits:
        return []
    base, extra = divmod(bits, count)
    out: list[str] = []
    consumed = 0
    for i in range(count):
        size = base + (1 if i < extra else 0)
        shift = bits - consumed - size
        out.append(format((number >> shift) & ((1 << size) - 1), "x"))
        consumed += size
    return out


def _photo_candidate_query(scope: list[str] | None, phash: str, dhash: str) -> dict:
    prefix = {"source_key": {"$in": scope}} if scope else {}
    ors: list[dict[str, Any]] = []
    for value in (phash, dhash):
        chunks = _chunks(value)
        if chunks:
            ors.append({"phash_chunks": {"$in": chunks}})
            ors.append({"dhash_chunks": {"$in": chunks}})
    if not ors:
        return {**prefix, "phash": {"$exists": True, "$ne": None}}
    return {**prefix, "$or": ors}


def _legacy_photo_candidate_query(scope: list[str] | None) -> dict:
    prefix = {"source_key": {"$in": scope}} if scope else {}
    return {
        **prefix,
        "$or": [
            {"phash_chunks": {"$exists": False}, "phash": {"$exists": True, "$ne": None}},
            {"dhash_chunks": {"$exists": False}, "dhash": {"$exists": True, "$ne": None}},
        ],
    }


def _photo_score(query_hash, candidate: dict) -> tuple[float, int | None, int | None]:
    phash = str(candidate.get("phash") or "")
    dhash = str(candidate.get("dhash") or "")
    p = hamming_hex(query_hash.phash, phash)
    d = hamming_hex(query_hash.dhash, dhash)

    metrics: list[tuple[float, float]] = []
    for left, right, weight in (
        (query_hash.phash, candidate.get("phash"), 0.40),
        (query_hash.dhash, candidate.get("dhash"), 0.25),
        (query_hash.whash, candidate.get("whash"), 0.10),
        (query_hash.phash_large, candidate.get("phash_large"), 0.15),
        (query_hash.colorhash, candidate.get("colorhash"), 0.10),
    ):
        distance = hamming_hex(left, right)
        if distance is None:
            continue
        bits = max(len(str(left)), len(str(right))) * 4
        metrics.append((max(0.0, 1.0 - distance / max(1, bits)), weight))

    if not metrics:
        return 0.0, p, d

    weighted = sum(sim * weight for sim, weight in metrics)
    total = sum(weight for _, weight in metrics)
    score = weighted / total if total else 0.0
    return score, p, d


async def _photo_hash_match(
    media_hash,
    scope: list[str] | None,
    *,
    global_mode: bool = False,
):
    if not media_hash.phash and not media_hash.dhash:
        return None, 0.0

    projection = {
        "_id": 1,
        "name": 1,
        "command": 1,
        "source_key": 1,
        "media_type": 1,
        "phash": 1,
        "phash_large": 1,
        "dhash": 1,
        "whash": 1,
        "colorhash": 1,
    }

    async def rank(cursor):
        ranked: list[tuple[float, int | None, int | None, dict]] = []
        async for candidate in cursor:
            if str(candidate.get("media_type") or "photo").lower() not in {"photo", "image"}:
                continue
            score, p_distance, d_distance = _photo_score(media_hash, candidate)
            if p_distance is None and d_distance is None:
                continue
            ranked.append((score, p_distance, d_distance, candidate))
        ranked.sort(key=lambda row: row[0], reverse=True)
        return ranked

    async def accept(ranked):
        if not ranked:
            return None, 0.0
        best = ranked[0]
        second_score = ranked[1][0] if len(ranked) > 1 else 0.0
        threshold = _PHASH_MIN_SCORE if global_mode else _PHASH_MIN_SCORE - 0.01
        margin = best[0] - second_score
        structural_ok = (
            best[1] is not None and best[1] <= _PHASH_THRESHOLD
        ) or (
            best[2] is not None and best[2] <= 12
        )
        if not structural_ok or best[0] < threshold:
            return None, best[0]
        if len(ranked) > 1 and margin < _PHASH_MIN_MARGIN:
            log.warning(
                "pHash ambiguous source=%s best=%s second=%s margin=%.4f",
                best[3].get("source_key"),
                best[3].get("name"),
                ranked[1][3].get("name"),
                margin,
            )
            return None, best[0]
        return best[3], best[0]

    ranked = await rank(
        characters.find(
            _photo_candidate_query(scope, media_hash.phash or "", media_hash.dhash or ""),
            projection,
        ).limit(_HASH_CANDIDATE_LIMIT)
    )
    doc, score = await accept(ranked)
    if doc:
        return doc, score

    # Compatibility pass for old records that have pHash fields but no chunk
    # index. This is only reached after the indexed candidate pass is not safe.
    legacy_ranked = await rank(
        characters.find(
            _legacy_photo_candidate_query(scope),
            projection,
        ).limit(_HASH_CANDIDATE_LIMIT)
    )
    return await accept(legacy_ranked)


async def _download(bot: Bot, file_id: str) -> bytes | None:
    if not file_id:
        return None
    async with _HASH_DOWNLOAD_SEM:
        try:
            result = await asyncio.wait_for(bot.download(file_id), timeout=45)
        except Exception as exc:
            log.info("hash fallback download failed: %s", exc)
            return None
        if isinstance(result, io.BytesIO):
            return result.getvalue()
        if hasattr(result, "read"):
            value = result.read()
            return value if isinstance(value, bytes) else None
        return None


async def _hash_fallback(
    bot: Bot,
    media,
    source_message: Message,
    collections: list[str],
    *,
    allow_global_fallback: bool,
):
    file_id = str(getattr(media.obj, "file_id", "") or "").strip()
    if not file_id:
        return None, "no_file_id"

    data = await _download(bot, file_id)
    if not data:
        return None, "hash_download_failed"

    media_hash = await asyncio.to_thread(
        hash_photo if media.media_type == "photo" else hash_video,
        data,
    )

    # Video signature is an exact content fingerprint over the sampled
    # frames. It is especially important for video messages whose Telegram UID
    # was not present in an older imported record.
    if media.media_type == "video" and media_hash.video_signature:
        doc = await _video_signature_find(collections, media_hash.video_signature)
        if doc:
            return doc, "video_signature"

        if allow_global_fallback:
            global_docs = await _video_signature_global_candidates(
                media_hash.video_signature,
                limit=2,
            )
            if len(global_docs) == 1:
                return global_docs[0], "video_signature_global"
            if len(global_docs) > 1:
                log.warning(
                    "VIDEO signature global recovery ambiguous message=%s candidates=%s",
                    getattr(source_message, "message_id", None),
                    len(global_docs),
                )

    # SHA-256 is byte-exact. It is the first fallback after Telegram UID.
    if media_hash.sha256:
        doc = await _hash_exact_find(collections, media_hash.sha256)
        if doc:
            return doc, "sha256"

        if allow_global_fallback:
            global_docs = await _hash_global_candidates(media_hash.sha256, limit=2)
            if len(global_docs) == 1:
                return global_docs[0], "sha256_global"
            if len(global_docs) > 1:
                log.warning(
                    "SHA global recovery ambiguous message=%s candidates=%s",
                    getattr(source_message, "message_id", None),
                    len(global_docs),
                )

    # Perceptual hashing is only for photos. It is similarity, not identity,
    # so it is source-scoped by default and requires a strong score + margin.
    if media.media_type == "photo":
        doc, score = await _photo_hash_match(
            media_hash,
            collections,
            global_mode=False,
        )
        if doc:
            return doc, f"phash:{score:.3f}"

        if allow_global_fallback:
            doc, score = await _photo_hash_match(
                media_hash,
                None,
                global_mode=True,
            )
            if doc:
                return doc, f"phash_global:{score:.3f}"

    return None, "hash_not_found"


async def lookup_message(bot: Bot, message: Message, *, allow_global_fallback: bool = False):
    """Lookup order: Telegram UID -> SHA-256 -> pHash.

    Auto lookup remains strictly source-scoped. Manual lookup performs the same
    source-scoped sequence first and may use the existing global fallback only
    after that sequence fails. pHash is never accepted on score alone: a
    structural hamming threshold and an ambiguity margin are both required.
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
        # LookupV4 hot path: source-aware RAM first, then local SQLite.
        doc = _ram_exact_find(uids, collections)
        if doc:
            log.info(
                "UID DEBUG ram_match message=%s source=%s name=%s",
                getattr(message, "message_id", None),
                doc.get("source_key"),
                doc.get("name"),
            )
            return doc, "uid_ram"

        doc = await lookup_index.lookup_source(uids, collections)
        if doc:
            lookup_index.ram.put(doc)
            log.info(
                "UID DEBUG sqlite_match message=%s source=%s name=%s",
                getattr(message, "message_id", None),
                doc.get("source_key"),
                doc.get("name"),
            )
            return doc, "uid_sqlite"

        doc = await _exact_find(collections, uids)
        if doc:
            log.info(
                "UID DEBUG source_match message=%s source=%s name=%s",
                getattr(message, "message_id", None),
                doc.get("source_key"),
                doc.get("name"),
            )
            return doc, "uid"

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

        # Forwarded-source recovery: keep this source-scoped and exact. This
        # does not replace Telegram UID identity; it only recovers legacy rows
        # whose source-origin is known but whose UID changed or was not imported.
        origin_doc = await _origin_exact_find(collections, source_message)
        if origin_doc:
            lookup_index.ram.put(origin_doc)
            origin = source_origin_key(source_message)
            log.info(
                "UID DEBUG source_origin_match message=%s source=%s origin=%s:%s name=%s",
                getattr(message, "message_id", None),
                origin_doc.get("source_key"),
                origin[0] if origin else None,
                origin[1] if origin else None,
                origin_doc.get("name"),
            )
            return origin_doc, "source_origin"

        # Direct bot-to-bot messages can have no forward_origin. If the source
        # bot's message was previously archived with source_origin, recover it
        # by a unique source-scoped source-message-id match.
        bot_origin_doc = await _bot_message_origin_fallback(collections, source_message)
        if bot_origin_doc:
            lookup_index.ram.put(bot_origin_doc)
            log.info(
                "UID DEBUG bot_source_message_match message=%s source=%s name=%s",
                getattr(message, "message_id", None),
                bot_origin_doc.get("source_key"),
                bot_origin_doc.get("name"),
            )
            return bot_origin_doc, "bot_source_message"

    # UID failed. Manual lookup and forwarded/saved media recovery may use
    # an exact global UID fallback. Source-scoped lookup always wins.
    if allow_global_fallback:
        sqlite_global = await lookup_index.lookup_global(uids, limit=3)
        sqlite_selected = _select_global_candidate(sqlite_global)
        if sqlite_selected:
            lookup_index.ram.put(sqlite_selected)
            log.info(
                "UID DEBUG sqlite_global_recovery message=%s source=%s name=%s",
                getattr(message, "message_id", None),
                sqlite_selected.get("source_key"),
                sqlite_selected.get("name"),
            )
            return sqlite_selected, "uid_sqlite_global_recovery"

        global_docs = await _exact_global_candidates(uids, limit=3)
        if len(global_docs) == 1:
            log.info(
                "UID DEBUG global_exact_recovery message=%s requested_sources=%s db_source=%s name=%s",
                getattr(message, "message_id", None),
                collections,
                global_docs[0].get("source_key"),
                global_docs[0].get("name"),
            )
            return global_docs[0], "uid_global_recovery"

        if len(global_docs) > 1:
            # When source scope is unavailable, prefer the primary Catch source
            # before treating the UID as ambiguous. This changes only the global
            # UID recovery selection; source-scoped lookup remains untouched.
            preferred = next(
                (
                    doc
                    for doc in global_docs
                    if str(doc.get("source_key") or "").strip().lower()
                    == "items_character_catcher"
                ),
                None,
            )
            if preferred:
                log.info(
                    "UID DEBUG global_exact_priority message=%s preferred_source=%s candidates=%s name=%s",
                    getattr(message, "message_id", None),
                    preferred.get("source_key"),
                    len(global_docs),
                    preferred.get("name"),
                )
                return preferred, "uid_global_recovery"

            log.warning(
                "UID global recovery ambiguous message=%s source=%s candidates=%s",
                getattr(message, "message_id", None),
                collections,
                len(global_docs),
            )
            # Do not cross-match an ambiguous Telegram UID when the preferred
            # Catch source is not among the exact global matches.

    # UID failed. Now download and compute hashes for BOTH auto and manual.
    # Auto remains source-scoped; manual may go global only when source is unknown.
    hash_scope = collections
    hash_global = bool(allow_global_fallback and not collections)
    doc, reason = await _hash_fallback(
        bot,
        media,
        source_message,
        hash_scope,
        allow_global_fallback=hash_global,
    )
    if doc:
        log.info(
            "HASH LOOKUP MATCH message=%s source=%s reason=%s name=%s",
            getattr(message, "message_id", None),
            doc.get("source_key"),
            reason,
            doc.get("name"),
        )
        return doc, reason

    return None, reason
