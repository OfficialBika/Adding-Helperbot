from __future__ import annotations

import asyncio
import io
import logging
import time
from pathlib import Path
from typing import Any

from aiogram import Bot
from aiogram.types import Message

from services.hash_service import hamming_hex, hash_photo_lookup, hash_photo_fast, hash_video, sha256_bytes
from services.source_resolver import resolve_lookup_scope
from unified.config import settings
from unified.store import characters
from unified.lookup_cache import positive_uid_cache
from unified.uid_index import lookup_global as sqlite_lookup_global
from unified.uid_index import lookup_hot_global as ram_lookup_global
from unified.uid_index import lookup_hot_source as ram_lookup_source
from unified.uid_index import lookup_source as sqlite_lookup_source
from unified.uid_index import persist_uid_mappings, remember_hot_source
from unified.hash_index import lookup_photo_candidates, is_ready as hash_index_ready
from utils.media import extract_media

log = logging.getLogger(__name__)

# Hash fallback is deliberately behind exact Telegram UID lookup.
# It downloads only when UID lookup has failed, and never replaces UID identity.
# Allow the 24-GB / 12-vCPU VPS to process more cold lookups concurrently.
# The semaphore protects Telegram download pressure without serializing the
# rest of the lookup pipeline. Keep this separate from hash/DB concurrency.
_HASH_FAST_DOWNLOAD_SEM = asyncio.Semaphore(24)
_FULL_DOWNLOAD_SEM = asyncio.Semaphore(6)
_HASH_FAST_CHUNK_SIZE = 256 * 1024
_HASH_FULL_CHUNK_SIZE = 1024 * 1024
# Keep the first similarity pass bounded. Chunk indexes already narrow the
# candidate set; a smaller cap prevents Python-side ranking from becoming the
# dominant cost on large source datasets.
_HASH_CANDIDATE_LIMIT = 400
_HASH_FAST_PHOTO_TARGET_DIM = 320
_HASH_FAST_PHOTO_MAX_DIM = 384
_PHASH_THRESHOLD = 8
_PHASH_MIN_SCORE = 0.84
_PHASH_MIN_MARGIN = 0.035
_UID_CACHE = positive_uid_cache


def _coerce_match_score(value: Any) -> tuple[float, str]:
    """Normalize matcher output for safe logging and result reasons.

    The matcher normally returns a numeric score, but older/live variants may
    return a reason string such as phash_ram:0.981. Logging must never raise
    a TypeError and prevent the lookup handler from sending its result.
    """
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        score = float(value)
        return score, f"phash_fast:{score:.3f}"

    text = str(value or "").strip()
    if text:
        tail = text.rsplit(":", 1)[-1]
        try:
            score = float(tail)
            return score, text
        except (TypeError, ValueError):
            pass
    return 0.0, text or "phash:0.000"


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

    projection = {
        "_id": 1,
        "name": 1,
        "command": 1,
        "source_key": 1,
        "media_type": 1,
    }

    # Catch source priority is a result-selection rule, not a reason to
    # serialize the two independent Mongo probes. Probe each source in parallel,
    # then deterministically prefer primary Catch over FW Catch. This removes
    # avoidable network round-trip time while preserving the exact requested
    # result when the same UID exists in both sources.
    ordered_scope = _ordered_uid_sources(scope or [])
    if ordered_scope and {
        "items_character_catcher",
        "items_character_catcher_fw",
    }.intersection(ordered_scope):
        async def find_source(source: str):
            base = {"source_key": source}
            # New records use the indexed file_unique_ids field. Try that first
            # because it is the hot path and avoids the slower legacy $or.
            doc = await characters.find_one(
                {**base, **_uid_query_new(uids)},
                projection,
            )
            if doc:
                return doc
            # Legacy records are still fully supported, but only pay for this
            # compatibility query after the fast indexed query misses.
            return await characters.find_one(
                {**base, **_uid_query_legacy(uids)},
                projection,
            )

        results = await asyncio.gather(
            *(find_source(source) for source in ordered_scope)
        )
        for doc in results:
            if doc:
                return doc
        return None

    prefix = {"source_key": {"$in": scope}} if scope else {}
    query = {
        **prefix,
        "$or": [
            _uid_query_new(uids),
            *_uid_query_legacy(uids)["$or"],
        ],
    }
    return await characters.find_one(query, projection)


def _cache_doc(
    doc: dict | None,
    uids: list[str],
    *,
    persist_index: bool = False,
) -> None:
    if not doc or not uids:
        return
    source = str(doc.get("source_key") or "").strip().lower() or None
    # Keep the positive cache source-scoped. Global UID recovery stays in Mongo
    # so an ambiguous UID can never be silently resolved to the wrong dataset.
    if not source:
        return
    _UID_CACHE.remember(uids, doc, source)
    # A successful lookup is also published to the RAM UID index immediately.
    # This is deliberately independent of the TTL cache: even if a process is
    # reloaded or a cache object is recreated, the same positive result can be
    # served from the local hot index after the first verified resolution.
    remember_hot_source(source, uids, doc)
    if persist_index:
        # SQLite persistence is intentionally asynchronous; it must never add
        # disk latency to the lookup response path.
        try:
            asyncio.create_task(persist_uid_mappings(source, uids, doc))
        except RuntimeError:
            # Unit/test callers without a running loop still get the RAM fast path.
            pass


async def _learn_verified_uids(doc: dict | None, uids: list[str]) -> None:
    """Persist UIDs proven by a successful exact/hash match into Mongo.

    Mongo remains the source of truth. Only native Telegram file_unique_ids from
    the current media are added, and only to the already-selected character
    document. $addToSet is idempotent, so retries cannot duplicate or replace
    existing identities.
    """
    if not doc or not uids:
        return

    document_id = doc.get("_id")
    source = str(doc.get("source_key") or "").strip().lower()
    if document_id is None or not source:
        log.warning(
            "UID LEARN skipped: matched document has no stable identity source=%s",
            source,
        )
        return

    values = list(dict.fromkeys(str(uid).strip() for uid in uids if str(uid).strip()))
    if not values:
        return

    try:
        result = await characters.update_one(
            {"_id": document_id, "source_key": source},
            {"$addToSet": {"file_unique_ids": {"$each": values}}},
        )
        modified = int(getattr(result, "modified_count", 0) or 0)
        matched = int(getattr(result, "matched_count", 0) or 0)
        if modified:
            log.info(
                "UID LEARNED source=%s name=%s added=%s",
                source,
                doc.get("name"),
                len(values),
            )
        elif matched:
            log.info(
                "UID LEARNED source=%s name=%s already_known=%s",
                source,
                doc.get("name"),
                len(values),
            )
    except Exception:
        # Learning is an accelerator/data-enrichment step. Never turn a verified
        # lookup success into a user-visible lookup failure if Mongo update fails.
        log.exception(
            "UID LEARN failed source=%s name=%s",
            source,
            doc.get("name"),
        )


def _schedule_uid_learning(doc: dict | None, uids: list[str]) -> None:
    """Queue Mongo UID learning without ever blocking the lookup reply."""
    try:
        task = asyncio.create_task(_learn_verified_uids(doc, uids))
    except RuntimeError:
        return

    def _done(completed: asyncio.Task) -> None:
        try:
            completed.result()
        except Exception:
            log.exception(
                "UID LEARN task failed source=%s name=%s",
                (doc or {}).get("source_key"),
                (doc or {}).get("name"),
            )

    task.add_done_callback(_done)


def _ordered_uid_sources(collections: list[str]) -> list[str]:
    """Return UID lookup sources in deterministic Catch-first order.

    Catch and forward-catch records intentionally live in separate Mongo
    collections. The same Telegram file_unique_id may legitimately exist in
    both collections, so source order must be explicit rather than delegated
    to Mongo's $in query result order.
    """
    normalized: list[str] = []
    for value in collections:
        source = str(value or "").strip().lower()
        if source and source not in normalized:
            normalized.append(source)

    catch_sources = {
        "items_character_catcher",
        "items_character_catcher_fw",
    }
    if not catch_sources.intersection(normalized):
        return normalized

    # A Catch lookup must always be able to fall through primary Catch -> FW
    # Catch even when the resolver initially returned only one of the two.
    ordered = [
        "items_character_catcher",
        "items_character_catcher_fw",
    ]
    ordered.extend(source for source in normalized if source not in ordered)
    return ordered


def _cache_lookup(uids: list[str], scope: list[str] | None) -> dict | None:
    if not scope:
        return None
    for uid in uids:
        for source in scope:
            cached = _UID_CACHE.get(uid, source)
            if cached:
                return {
                    "name": cached.name,
                    "command": cached.command,
                    "source_key": cached.source_key,
                    "media_type": cached.media_type,
                }
    return None


async def _exact_global_candidates(uids: list[str], limit: int = 2) -> list[dict]:
    if not uids:
        return []
    projection = {
        "_id": 1,
        "name": 1,
        "command": 1,
        "source_key": 1,
        "media_type": 1,
    }
    query = {
        "$or": [
            _uid_query_new(uids),
            *_uid_query_legacy(uids)["$or"],
        ],
    }

    # Global recovery has no resolver scope, so make Catch-first selection
    # explicit instead of depending on MongoDB natural result order.
    catch = await characters.find_one(
        {"source_key": "items_character_catcher", **query},
        projection,
    )
    if catch:
        return [catch]

    non_catch_limit = max(1, int(limit))
    return await characters.find(
        {"source_key": {"$ne": "items_character_catcher"}, **query},
        projection,
    ).limit(non_catch_limit).to_list(length=non_catch_limit)


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
    projection = {
        "_id": 1,
        "name": 1,
        "command": 1,
        "source_key": 1,
        "media_type": 1,
    }
    return await characters.find_one({**prefix, **_sha_query(sha)}, projection)


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


def _photo_match_identity(candidate: dict) -> tuple[str, str]:
    """Return the stable user-visible identity for hash ambiguity checks.

    Hash records can legitimately vary in command, media-type label (photo vs
    image), or invisible Unicode formatting while still representing the same
    character. Ambiguity must compare actual identities, not storage metadata.
    """
    import unicodedata

    name = unicodedata.normalize("NFKC", str(candidate.get("name") or ""))
    name = "".join(ch for ch in name if ch not in "\u200b\u200c\u200d\u200e\u200f\u2060\ufeff")
    name = " ".join(name.split()).casefold()
    return (
        str(candidate.get("source_key") or "").strip().lower(),
        name,
    )


def _accept_photo_candidates(
    ranked: list[tuple[float, int | None, int | None, dict]],
    *,
    global_mode: bool = False,
):
    """Accept a strong pHash match while ignoring duplicate records of one identity.

    A zero margin is normally a useful ambiguity signal. However, records that
    resolve to the same source/name/media identity are not competing user-visible
    results. Keep the best-scoring representative of each identity before
    applying the margin rule.
    """
    if not ranked:
        return None, 0.0

    representatives: dict[tuple[str, str, str], tuple[float, int | None, int | None, dict]] = {}
    duplicate_count = 0
    for row in ranked:
        identity = _photo_match_identity(row[3])
        previous = representatives.get(identity)
        if previous is None:
            representatives[identity] = row
        else:
            duplicate_count += 1
            if row[0] > previous[0]:
                representatives[identity] = row

    unique_ranked = sorted(representatives.values(), key=lambda row: row[0], reverse=True)
    best = unique_ranked[0]
    second_score = unique_ranked[1][0] if len(unique_ranked) > 1 else 0.0
    threshold = _PHASH_MIN_SCORE if global_mode else _PHASH_MIN_SCORE - 0.01
    margin = best[0] - second_score
    structural_ok = (
        best[1] is not None and best[1] <= _PHASH_THRESHOLD
    ) or (
        best[2] is not None and best[2] <= 12
    )
    if not structural_ok or best[0] < threshold:
        return None, best[0]

    if duplicate_count:
        log.info(
            "pHash duplicate identities collapsed source=%s name=%s duplicates=%s unique=%s",
            best[3].get("source_key"),
            best[3].get("name"),
            duplicate_count,
            len(unique_ranked),
        )

    if len(unique_ranked) > 1 and margin < _PHASH_MIN_MARGIN:
        log.warning(
            "pHash ambiguous source=%s best=%s second=%s margin=%.4f",
            best[3].get("source_key"),
            best[3].get("name"),
            unique_ranked[1][3].get("name"),
            margin,
        )
        return None, best[0]

    return best[3], best[0]


async def _photo_hash_match(
    media_hash,
    scope: list[str] | None,
    *,
    global_mode: bool = False,
    use_ram: bool = True,
    use_mongo: bool = True,
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

    def rank_candidates(candidates):
        ranked: list[tuple[float, int | None, int | None, dict]] = []
        for candidate in candidates:
            if str(candidate.get("media_type") or "photo").lower() not in {"photo", "image"}:
                continue
            score, p_distance, d_distance = _photo_score(media_hash, candidate)
            if p_distance is None and d_distance is None:
                continue
            ranked.append((score, p_distance, d_distance, candidate))
        ranked.sort(key=lambda row: row[0], reverse=True)
        return ranked

    async def accept(ranked):
        return _accept_photo_candidates(ranked, global_mode=global_mode)

    # RAM candidate index is the primary cold-hash accelerator once warmed.
    # Mongo remains the correctness/compatibility fallback.
    if use_ram and hash_index_ready():
        ram_started = time.perf_counter()
        ram_candidates = lookup_photo_candidates(
            scope,
            media_hash.phash,
            media_hash.dhash,
            limit=min(_HASH_CANDIDATE_LIMIT, 200),
        )
        ram_candidate_ms = (time.perf_counter() - ram_started) * 1000
        if ram_candidates:
            ram_rank_started = time.perf_counter()
            ram_ranked = rank_candidates(ram_candidates)
            ram_rank_ms = (time.perf_counter() - ram_rank_started) * 1000
            ram_doc, ram_score = await accept(ram_ranked)
            log.info(
                "HASH RAM TIMING candidates=%s candidate_ms=%.1f rank_ms=%.1f score=%.3f",
                len(ram_candidates),
                ram_candidate_ms,
                ram_rank_ms,
                ram_score,
            )
            if ram_doc:
                return ram_doc, f"phash_ram:{ram_score:.3f}"

    if not use_mongo:
        return None, locals().get("ram_score", 0.0)
    mongo_query_started = time.perf_counter()
    mongo_candidates = await characters.find(
        _photo_candidate_query(scope, media_hash.phash or "", media_hash.dhash or ""),
        projection,
    ).limit(_HASH_CANDIDATE_LIMIT).to_list(length=_HASH_CANDIDATE_LIMIT)
    mongo_query_ms = (time.perf_counter() - mongo_query_started) * 1000

    mongo_rank_started = time.perf_counter()
    ranked = rank_candidates(mongo_candidates)
    mongo_rank_ms = (time.perf_counter() - mongo_rank_started) * 1000
    log.info(
        "HASH MONGO MATCH TIMING candidates=%s query_ms=%.1f rank_ms=%.1f",
        len(mongo_candidates),
        mongo_query_ms,
        mongo_rank_ms,
    )
    doc, score = await accept(ranked)
    if doc:
        return doc, score

    # Compatibility pass for old records that have pHash fields but no chunk
    # index. This is only reached after the indexed candidate pass is not safe.
    legacy_candidates = await characters.find(
        _legacy_photo_candidate_query(scope),
        projection,
    ).limit(_HASH_CANDIDATE_LIMIT).to_list(length=_HASH_CANDIDATE_LIMIT)
    legacy_ranked = rank_candidates(legacy_candidates)
    return await accept(legacy_ranked)


def _fast_photo_variant(source_message: Message):
    """Pick a small/medium Telegram PhotoSize for the first similarity pass.

    Telegram exposes multiple PhotoSize variants for normal photos. Downloading
    a large variant just to calculate a perceptual hash can add substantial
    transfer latency. Prefer the PhotoSize closest to a ~320px target (without
    exceeding 384px); otherwise use the smallest available variant. The
    original/largest variant remains available for exact SHA-256 fallback.
    """
    photos = [
        photo
        for photo in (getattr(source_message, "photo", None) or [])
        if getattr(photo, "file_id", None)
    ]
    if not photos:
        return None

    def dimensions(photo):
        width = int(getattr(photo, "width", 0) or 0)
        height = int(getattr(photo, "height", 0) or 0)
        return width, height, width * height

    suitable = [
        photo
        for photo in photos
        if max(dimensions(photo)[:2]) <= _HASH_FAST_PHOTO_MAX_DIM
    ]
    if suitable:
        # Prefer a preview close to 320px instead of the largest <=768px.
        # pHash/dHash do not need the larger preview for the first pass.
        return min(
            suitable,
            key=lambda photo: (
                abs(max(dimensions(photo)[:2]) - _HASH_FAST_PHOTO_TARGET_DIM),
                dimensions(photo)[2],
            ),
        )
    return min(photos, key=lambda photo: dimensions(photo)[2])


def _path_is_within(path: Path, root: Path) -> bool:
    """Return True only when path resolves to root itself or a child of root."""
    try:
        resolved_path = path.resolve()
        resolved_root = root.resolve()
        return resolved_path == resolved_root or resolved_root in resolved_path.parents
    except OSError:
        return False


async def _download(
    bot: Bot,
    file_id: str,
    *,
    timeout: float | None = None,
    priority: str = "fast",
) -> bytes | None:
    if not file_id:
        return None

    if priority == "full":
        semaphore = _FULL_DOWNLOAD_SEM
        chunk_size = _HASH_FULL_CHUNK_SIZE
    else:
        semaphore = _HASH_FAST_DOWNLOAD_SEM
        chunk_size = _HASH_FAST_CHUNK_SIZE

    wait_started = time.perf_counter()
    async with semaphore:
        wait_ms = (time.perf_counter() - wait_started) * 1000
        transfer_started = time.perf_counter()

        # Local Bot API mode can return an absolute filesystem path from getFile().
        # Reading that path directly removes the second HTTP transfer from the
        # lookup hot path. The safety root is mandatory for direct reads; any
        # mismatch falls back to the existing aiogram download path.
        if getattr(settings, "bot_api_is_local", False):
            local_started = time.perf_counter()
            try:
                file = await bot.get_file(file_id)
                raw_path = str(getattr(file, "file_path", "") or "").strip()
                local_path = Path(raw_path) if raw_path else None
                root_raw = str(getattr(settings, "bot_api_local_files_root", "") or "").strip()
                root = Path(root_raw).expanduser() if root_raw else None

                if (
                    local_path is not None
                    and local_path.is_absolute()
                    and root is not None
                    and _path_is_within(local_path, root)
                ):
                    read_started = time.perf_counter()
                    data = await asyncio.to_thread(local_path.read_bytes)
                    get_file_ms = (read_started - local_started) * 1000
                    read_ms = (time.perf_counter() - read_started) * 1000
                    total_ms = (time.perf_counter() - transfer_started) * 1000
                    log.info(
                        "HASH DOWNLOAD TIMING priority=%s wait_ms=%.1f getfile_ms=%.1f local_read_ms=%.1f total_ms=%.1f bytes=%s mode=local_file",
                        priority,
                        wait_ms,
                        get_file_ms,
                        read_ms,
                        total_ms,
                        len(data),
                    )
                    return data

                log.info(
                    "Local Bot API file path not used file_id=%s path_absolute=%s root_configured=%s",
                    file_id,
                    bool(local_path and local_path.is_absolute()),
                    bool(root),
                )
            except Exception as exc:
                local_ms = (time.perf_counter() - local_started) * 1000
                log.info(
                    "Local Bot API direct read failed file_id=%s local_ms=%.1f error=%s; falling back to HTTP download",
                    file_id,
                    local_ms,
                    exc,
                )

        try:
            result = await bot.download(
                file_id,
                timeout=int(timeout or getattr(settings, "download_timeout_seconds", 20)),
                chunk_size=chunk_size,
            )
        except Exception as exc:
            transfer_ms = (time.perf_counter() - transfer_started) * 1000
            log.info(
                "HASH DOWNLOAD TIMING priority=%s wait_ms=%.1f transfer_ms=%.1f total_ms=%.1f result=failed error=%s",
                priority, wait_ms, transfer_ms, wait_ms + transfer_ms, exc,
            )
            return None

        transfer_ms = (time.perf_counter() - transfer_started) * 1000
        if isinstance(result, io.BytesIO):
            data = result.getvalue()
        elif hasattr(result, "read"):
            value = result.read()
            data = value if isinstance(value, bytes) else None
        else:
            data = None

        log.info(
            "HASH DOWNLOAD TIMING priority=%s wait_ms=%.1f transfer_ms=%.1f total_ms=%.1f bytes=%s",
            priority, wait_ms, transfer_ms, wait_ms + transfer_ms, len(data) if data is not None else 0,
        )
        return data

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

    # PHOTO FAST PATH:
    # A Telegram photo normally has several PhotoSize variants. Use a
    # small/medium variant first, so a cold lookup does not download the
    # largest image merely to calculate pHash/dHash. If similarity is strong,
    # return immediately and learn every native UID from the original message.
    # Only ambiguous/missed matches pay the full-resolution download cost.
    if media.media_type == "photo":
        fast_media = _fast_photo_variant(source_message)
        fast_file_id = str(getattr(fast_media, "file_id", "") or "").strip()
        if fast_file_id:
            fast_download_started = time.perf_counter()
            fast_data = await _download(bot, fast_file_id, priority="fast")
            fast_download_ms = (time.perf_counter() - fast_download_started) * 1000
            if fast_data:
                fast_hash_started = time.perf_counter()
                fast_hash = await asyncio.to_thread(hash_photo_fast, fast_data)
                fast_hash_ms = (time.perf_counter() - fast_hash_started) * 1000
                fast_match_started = time.perf_counter()
                fast_doc, fast_score = await _photo_hash_match(
                    fast_hash,
                    collections,
                    global_mode=False,
                    use_ram=True,
                    use_mongo=False,
                )
                fast_match_ms = (time.perf_counter() - fast_match_started) * 1000
                fast_score_value, fast_reason = _coerce_match_score(fast_score)
                log.info(
                    "HASH FAST TIMING message=%s variant=%sx%s download_ms=%.1f hash_ms=%.1f match_ms=%.1f reason=%s score=%.3f",
                    getattr(source_message, "message_id", None),
                    getattr(fast_media, "width", 0),
                    getattr(fast_media, "height", 0),
                    fast_download_ms,
                    fast_hash_ms,
                    fast_match_ms,
                    fast_reason,
                    fast_score_value,
                )
                if fast_doc:
                    return fast_doc, fast_reason

                # The RAM shortlist did not produce a safe match. Start the
                # full-resolution download and the Mongo perceptual lookup at
                # the same time so the two ~1-2s stages do not become serial.
                full_download_task = asyncio.create_task(
                    _download(bot, file_id, priority="full")
                )
                mongo_match_task = asyncio.create_task(
                    _photo_hash_match(
                        fast_hash,
                        collections,
                        global_mode=False,
                        use_ram=False,
                        use_mongo=True,
                    )
                )
                try:
                    mongo_doc, mongo_score = await mongo_match_task
                except Exception:
                    log.exception(
                        "HASH MONGO MATCH task failed message=%s",
                        getattr(source_message, "message_id", None),
                    )
                    mongo_doc, mongo_score = None, 0.0
                if mongo_doc:
                    full_download_task.cancel()
                    try:
                        await full_download_task
                    except asyncio.CancelledError:
                        pass
                    return mongo_doc, f"phash_fast_mongo:{mongo_score:.3f}"
                data = await full_download_task
                download_ms = 0.0
                if data is not None:
                    # The actual transfer timing is already emitted by _download.
                    # Keep the full-stage processing below without downloading twice.
                    pass
                else:
                    log.info(
                        "HASH FULL TIMING message=%s result=download_failed_after_overlap",
                        getattr(source_message, "message_id", None),
                    )
                    return None, "hash_download_failed"
                download_ms = 0.0

    # FULL FALLBACK:
    # Needed for exact SHA-256 recovery, legacy records that are not found by
    # the fast perceptual pass, or ambiguous similarity cases. This preserves
    # the existing exact-match semantics instead of replacing them with a
    # perceptual-only lookup.
    started = time.perf_counter()
    if 'data' not in locals():
        download_started = started
        data = await _download(bot, file_id, priority="full")
        download_ms = (time.perf_counter() - download_started) * 1000
    else:
        download_ms = 0.0
    if not data:
        log.info("HASH TIMING message=%s download_ms=%.1f result=download_failed", getattr(source_message, "message_id", None), download_ms)
        return None, "hash_download_failed"

    # Exact bytes are the strongest and cheapest full-fallback test.
    # Do not calculate expensive perceptual hashes until exact SHA-256 misses.
    sha_hash_started = time.perf_counter()
    sha256 = await asyncio.to_thread(sha256_bytes, data)
    sha_hash_ms = (time.perf_counter() - sha_hash_started) * 1000

    sha_started = time.perf_counter()
    doc = await _hash_exact_find(collections, sha256)
    sha_ms = (time.perf_counter() - sha_started) * 1000
    if doc:
        log.info(
            "HASH EXACT TIMING message=%s sha_hash_ms=%.1f sha_db_ms=%.1f",
            getattr(source_message, "message_id", None), sha_hash_ms, sha_ms,
        )
        return doc, "sha256"

    if allow_global_fallback:
        global_sha_started = time.perf_counter()
        global_docs = await _hash_global_candidates(sha256, limit=2)
        global_sha_ms = (time.perf_counter() - global_sha_started) * 1000
        if len(global_docs) == 1:
            log.info(
                "HASH EXACT GLOBAL TIMING message=%s sha_hash_ms=%.1f sha_db_ms=%.1f",
                getattr(source_message, "message_id", None), sha_hash_ms, global_sha_ms,
            )
            return global_docs[0], "sha256_global"
        if len(global_docs) > 1:
            log.warning(
                "SHA global recovery ambiguous message=%s candidates=%s",
                getattr(source_message, "message_id", None), len(global_docs),
            )

    hash_started = time.perf_counter()
    media_hash = await asyncio.to_thread(
        hash_photo_lookup if media.media_type == "photo" else hash_video,
        data,
    )
    hash_ms = (time.perf_counter() - hash_started) * 1000

    phash_task = None
    if media.media_type == "photo":
        phash_task = asyncio.create_task(
            _photo_hash_match(
                media_hash,
                collections,
                global_mode=False,
            )
        )

    log.info(
        "HASH FULL TIMING message=%s download_ms=%.1f sha_hash_ms=%.1f sha_db_ms=%.1f perceptual_hash_ms=%.1f",
        getattr(source_message, "message_id", None),
        download_ms,
        sha_hash_ms,
        sha_ms,
        hash_ms,
    )
    # Perceptual hashing is only for photos. It is similarity, not identity,
    # so it is source-scoped by default and requires a strong score + margin.
    if phash_task is not None:
        phash_started = time.perf_counter()
        doc, score = await phash_task
        phash_ms = (time.perf_counter() - phash_started) * 1000
        log.info(
            "HASH TIMING message=%s download_ms=%.1f hash_ms=%.1f sha_ms=%.1f phash_ms=%.1f",
            getattr(source_message, "message_id", None),
            download_ms,
            hash_ms,
            locals().get("sha_ms", 0.0),
            phash_ms,
        )
        if doc:
            return doc, f"phash:{score:.3f}"

        # With an explicitly allowed global/manual lookup and no source scope,
        # perform the global similarity pass only after the source-scoped pass.
        if allow_global_fallback and not collections:
            global_phash_started = time.perf_counter()
            doc, score = await _photo_hash_match(
                media_hash,
                None,
                global_mode=True,
            )
            global_phash_ms = (time.perf_counter() - global_phash_started) * 1000
            if doc:
                return doc, f"phash_global:{score:.3f}"

    return None, "hash_not_found"


async def lookup_message(bot: Bot, message: Message, *, allow_global_fallback: bool = False):
    """Lookup order: Telegram UID -> RAM/SQLite -> exact Mongo UID -> hash fallback.

    Photo hash fallback uses a small Telegram preview first. If that does not
    produce a safe match, the full media is downloaded, exact SHA-256 is checked
    first, and only then are expensive perceptual hashes used. Auto lookup
    remains source-scoped; manual lookup may use the existing global fallback.
    pHash is never accepted on score alone: structural hamming and ambiguity
    checks are still required.
    """
    media = extract_media(message)
    if not media:
        return None, "no_media"

    source_message = media.source_message
    collections = _ordered_uid_sources(_scope(source_message))
    if not collections and not allow_global_fallback:
        return None, "source_unknown"

    uids = _telegram_uids(source_message, media.media_type, media.obj)
    if not uids:
        return None, "no_file_unique_id"

    # Catch lookups intentionally use the deterministic source order above:
    # items_character_catcher -> items_character_catcher_fw -> other sources.
    cached_doc = _cache_lookup(uids, collections)
    if cached_doc:
        log.info(
            "UID CACHE HIT message=%s collections=%s uids=%s",
            getattr(message, "message_id", None), collections, uids,
        )
        return cached_doc, "uid_cache"

    # Process-local exact UID index is the first persistent-data accelerator.
    # It is populated from SQLite at startup and updated on every UID upsert.
    # MongoDB remains authoritative, so RAM/SQLite misses always fall through.
    if collections:
        ram_doc = ram_lookup_source(collections, uids)
        if ram_doc:
            log.info(
                "UID RAM HOT HIT message=%s source=%s name=%s",
                getattr(message, "message_id", None),
                ram_doc.get("source_key"),
                ram_doc.get("name"),
            )
            _cache_doc(ram_doc, uids)
            return ram_doc, "uid_ram"

        sqlite_doc = await sqlite_lookup_source(collections, uids)
        if sqlite_doc:
            log.info(
                "UID SQLITE HIT message=%s source=%s name=%s",
                getattr(message, "message_id", None),
                sqlite_doc.get("source_key"),
                sqlite_doc.get("name"),
            )
            _cache_doc(sqlite_doc, uids)
            return sqlite_doc, "uid_sqlite"

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
            _cache_doc(doc, uids, persist_index=True)
            return doc, "uid"

        # Source-scoped auto lookup must not perform an extra global probe.
        # If global recovery is explicitly allowed, the actual global query
        # below is the only global round-trip needed.
        if not allow_global_fallback:
            log.warning(
                "UID DEBUG database_uid_miss message=%s requested_sources=%s",
                getattr(message, "message_id", None),
                collections,
            )

    # UID failed. Manual lookup and forwarded/saved media recovery may use
    # an exact global UID fallback. This is safe because file_unique_id is
    # Telegram's native exact media identity. Source-scoped lookup always wins.
    if allow_global_fallback:
        # Try the RAM exact-UID index before SQLite/Mongo global recovery.
        global_docs = ram_lookup_global(uids, limit=2)
        if len(global_docs) == 1:
            _cache_doc(global_docs[0], uids, persist_index=True)
            return global_docs[0], "uid_ram_global"

        # Try the persistent local exact-UID index before Mongo recovery.
        global_docs = await sqlite_lookup_global(uids, limit=2)
        if len(global_docs) == 1:
            _cache_doc(global_docs[0], uids, persist_index=True)
            return global_docs[0], "uid_sqlite_global"
        if len(global_docs) > 1:
            # Keep the same ambiguity rules as Mongo; SQLite only accelerates.
            preferred = next(
                (
                    doc for doc in global_docs
                    if str(doc.get("source_key") or "").strip().lower()
                    == "items_character_catcher"
                ),
                None,
            )
            if preferred:
                _cache_doc(preferred, uids, persist_index=True)
                return preferred, "uid_sqlite_global"
            log.warning(
                "UID SQLite global recovery ambiguous message=%s candidates=%s",
                getattr(message, "message_id", None),
                len(global_docs),
            )
        global_docs = await _exact_global_candidates(uids, limit=2)
        if len(global_docs) == 1:
            log.info(
                "UID DEBUG global_exact_recovery message=%s requested_sources=%s db_source=%s name=%s",
                getattr(message, "message_id", None),
                collections,
                global_docs[0].get("source_key"),
                global_docs[0].get("name"),
            )
            _cache_doc(global_docs[0], uids, persist_index=True)
            _schedule_uid_learning(global_docs[0], uids)
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
                _cache_doc(preferred, uids, persist_index=True)
                _schedule_uid_learning(preferred, uids)
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
        # A hash match is a positive lookup result. Cache the original Telegram
        # UID against that result so the same media never needs another download,
        # hash computation, or Mongo similarity scan during the cache TTL.
        _cache_doc(doc, uids, persist_index=True)
        # Hash has now positively identified the character. Learn the current
        # Telegram UIDs in Mongo as an idempotent background enrichment so
        # future lookups can resolve by native UID without downloading media.
        _schedule_uid_learning(doc, uids)
        log.info(
            "HASH LOOKUP MATCH message=%s source=%s reason=%s name=%s",
            getattr(message, "message_id", None),
            doc.get("source_key"),
            reason,
            doc.get("name"),
        )
        return doc, reason

    return None, reason
