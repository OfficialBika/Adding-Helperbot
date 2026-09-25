from __future__ import annotations

import asyncio
import io
import logging
from typing import Any

from aiogram import Bot
from aiogram.types import Message

from services.hash_service import hamming_hex, hash_photo, hash_video
from services.source_resolver import resolve_lookup_scope
from unified.config import settings
from unified.store import characters
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
    # Legacy records may have hashes without chunk indexes.
    ors.extend([
        {"phash": {"$exists": True, "$ne": None}},
        {"dhash": {"$exists": True, "$ne": None}},
    ])
    return {**prefix, "$or": ors}


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

    cursor = characters.find(
        _photo_candidate_query(scope, media_hash.phash or "", media_hash.dhash or ""),
        {
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
        },
    ).limit(_HASH_CANDIDATE_LIMIT)

    ranked: list[tuple[float, int | None, int | None, dict]] = []
    async for candidate in cursor:
        if str(candidate.get("media_type") or "photo").lower() not in {"photo", "image"}:
            continue
        score, p_distance, d_distance = _photo_score(media_hash, candidate)
        if p_distance is None and d_distance is None:
            continue
        ranked.append((score, p_distance, d_distance, candidate))

    ranked.sort(key=lambda row: row[0], reverse=True)
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

    if not allow_global_fallback:
        return None, "not_found_uid"

    # Exact global UID recovery is retained before any download.
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
        # Do not cross-match an ambiguous Telegram UID.

    # UID failed. Only now download and compute hashes.
    hash_scope = collections
    if not hash_scope:
        hash_scope = []

    doc, reason = await _hash_fallback(
        bot,
        media,
        source_message,
        hash_scope,
        allow_global_fallback=allow_global_fallback,
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
