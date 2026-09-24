from __future__ import annotations

import asyncio
import io
import logging

from aiogram import Bot
from aiogram.types import Message

from unified.config import settings
from unified.store import characters, _chunks
from services.hash_service import hash_photo, hash_video, hamming_hex
from services.source_resolver import resolve_lookup_scope
from utils.media import extract_media

log = logging.getLogger(__name__)

def _scope(message: Message) -> list[str] | None:
    try:
        scope = resolve_lookup_scope(message)
        values = [str(x).strip().lower() for x in (scope.collections or []) if str(x).strip()]
        return values or None
    except Exception as exc:
        log.info("source scope unavailable: %s", exc)
        return None

async def _download(bot: Bot, file_id: str) -> bytes | None:
    if not file_id:
        return None
    try:
        result = await asyncio.wait_for(bot.download(file_id), timeout=20)
        if isinstance(result, io.BytesIO):
            return result.getvalue()
        if hasattr(result, "read"):
            value = result.read()
            return value if isinstance(value, bytes) else bytes(value)
    except Exception as exc:
        log.info("media download failed: %s", exc)
    return None

async def _find_exact(
    file_uids: list[str] | None,
    file_ids: list[str] | None,
    sha: str | None,
    origin,
    scope,
):
    """Fast exact lookup.

    UID lookup is deliberately a separate first query instead of one large
    $or. This lets MongoDB use the multikey UID index directly and avoids
    repeating the same file-id clauses for every photo variant.
    """
    uids = list(dict.fromkeys(str(x).strip() for x in (file_uids or []) if str(x).strip()))
    fids = list(dict.fromkeys(str(x).strip() for x in (file_ids or []) if str(x).strip()))

    def scoped(base: dict, values: list[str] | None = None) -> dict:
        query = dict(base)
        if scope:
            query["source_key"] = {"$in": scope}
        return query

    # 1) Telegram file_unique_id: the cheapest and strongest exact media key.
    if uids:
        doc = await characters.find_one(
            scoped({"file_unique_ids": {"$in": uids}})
        )
        if doc:
            return doc

        # Legacy records may only have the scalar canonical UID.
        doc = await characters.find_one(
            scoped({"telegram_file_unique_id": {"$in": uids}})
        )
        if doc:
            return doc

        # Only use global UID matching when the source scope cannot resolve it.
        if scope:
            doc = await characters.find_one({"file_unique_ids": {"$in": uids}})
            if doc:
                return doc
            doc = await characters.find_one({"telegram_file_unique_id": {"$in": uids}})
            if doc:
                return doc

    # 2) file_id is useful for same-bot messages and old records.
    if fids:
        doc = await characters.find_one(
            scoped({"file_ids": {"$in": fids}})
        )
        if doc:
            return doc

        doc = await characters.find_one(
            scoped({"telegram_file_id": {"$in": fids}})
        )
        if doc:
            return doc

        if scope:
            doc = await characters.find_one({"file_ids": {"$in": fids}})
            if doc:
                return doc
            doc = await characters.find_one({"telegram_file_id": {"$in": fids}})
            if doc:
                return doc

    # 3) SHA-256 is the next exact identity after Telegram IDs.
    if sha:
        doc = await characters.find_one(scoped({"sha256": sha}))
        if doc:
            return doc
        doc = await characters.find_one(scoped({"sha256_aliases": sha}))
        if doc:
            return doc
        if scope:
            doc = await characters.find_one({"sha256": sha})
            if doc:
                return doc
            doc = await characters.find_one({"sha256_aliases": sha})
            if doc:
                return doc

    # 4) Forward origin is a final exact fallback.
    if origin:
        query = {
            "source_origin.chat_id": origin[0],
            "source_origin.message_id": origin[1],
        }
        doc = await characters.find_one(scoped(query))
        if doc:
            return doc
        if scope:
            doc = await characters.find_one(query)
            if doc:
                return doc

    return None

def _similarity(query_hash, item) -> float:
    metrics = []
    for a, b, weight in (
        (query_hash.phash, item.get("phash"), 0.35),
        (query_hash.dhash, item.get("dhash"), 0.25),
        (query_hash.whash, item.get("whash"), 0.15),
        (query_hash.phash_large, item.get("phash_large"), 0.15),
        (query_hash.colorhash, item.get("colorhash"), 0.10),
    ):
        distance = hamming_hex(a, b)
        if distance is not None:
            bits = max(1, len(str(a)) * 4)
            metrics.append((max(0.0, 1.0 - distance / bits), weight))
    return (
        sum(score * weight for score, weight in metrics) / sum(weight for _, weight in metrics)
        if metrics else 0.0
    )

async def _photo_similarity(hashed, scope):
    chunk_values = set(_chunks(hashed.phash)) | set(_chunks(hashed.dhash))
    if not chunk_values:
        return None

    base = {
        "$or": [
            {"phash_chunks": {"$in": list(chunk_values)}},
            {"dhash_chunks": {"$in": list(chunk_values)}},
        ]
    }

    async def search(query):
        best = None
        best_score = 0.0
        async for item in characters.find(query, {
            "name": 1, "command": 1, "source_key": 1,
            "phash": 1, "phash_large": 1, "dhash": 1,
            "whash": 1, "colorhash": 1,
        }).limit(settings.max_photo_candidates):
            score = _similarity(hashed, item)
            p = hamming_hex(hashed.phash, item.get("phash"))
            d = hamming_hex(hashed.dhash, item.get("dhash"))
            if (
                (p is not None and p <= settings.photo_threshold)
                or (d is not None and d <= settings.dhash_threshold)
            ) and score >= 0.80 and score > best_score:
                best, best_score = item, score
        return best

    if scope:
        found = await search({**base, "source_key": {"$in": scope}})
        if found:
            return found

    # Source unknown? Use the global chunk indexes as a fallback.
    return await search(base)

async def _video_similarity(hashed, scope):
    if hashed.video_signature:
        query = {"video_signature": hashed.video_signature}
        if scope:
            doc = await characters.find_one({**query, "source_key": {"$in": scope}})
            if doc:
                return doc
        doc = await characters.find_one(query)
        if doc:
            return doc

    if not hashed.duration_ms:
        return None

    second = round(hashed.duration_ms / 1000)
    base = {
        "media_type": "video",
        "duration_bucket": {"$gte": max(0, second - 4), "$lte": second + 4},
    }

    async def search(query):
        best = None
        best_avg = float("inf")
        async for item in characters.find(query, {
            "name": 1, "command": 1, "source_key": 1,
            "video_samples": 1,
        }).limit(settings.max_video_candidates):
            distances = []
            bypos = {
                round(float(sample.get("position", 0.0)), 3): sample
                for sample in item.get("video_samples", [])
            }
            for sample in hashed.video_samples:
                other = bypos.get(round(float(sample.position), 3))
                if other:
                    for left, right in (
                        (sample.phash, other.get("phash")),
                        (sample.dhash, other.get("dhash")),
                    ):
                        distance = hamming_hex(left, right)
                        if distance is not None:
                            distances.append(distance)
            if distances:
                average = sum(distances) / len(distances)
                minimum = min(distances)
                if (
                    minimum <= settings.video_frame_threshold
                    and average <= settings.video_avg_threshold
                    and average < best_avg
                ):
                    best, best_avg = item, average
        return best

    if scope:
        found = await search({**base, "source_key": {"$in": scope}})
        if found:
            return found
    return await search(base)

async def lookup_message(bot: Bot, message: Message):
    media = extract_media(message)
    if not media:
        return None, "no_media"

    source_message = media.source_message
    scope = _scope(source_message)
    photo_uids = []
    photo_file_ids = []
    if media.media_type == "photo":
        for p in (getattr(source_message, "photo", None) or []):
            u = str(getattr(p, "file_unique_id", "") or "").strip()
            f = str(getattr(p, "file_id", "") or "").strip()
            if u: photo_uids.append(u)
            if f: photo_file_ids.append(f)

    uid = str(getattr(media.obj, "file_unique_id", "") or "").strip()
    fid = str(getattr(media.obj, "file_id", "") or "").strip()
    if uid and uid not in photo_uids: photo_uids.append(uid)
    if fid and fid not in photo_file_ids: photo_file_ids.append(fid)

    origin = None
    try:
        origin_obj = getattr(source_message, "forward_origin", None)
        chat = getattr(origin_obj, "chat", None) or getattr(origin_obj, "sender_chat", None)
        mid = getattr(origin_obj, "message_id", None)
        if chat and mid is not None:
            origin = (int(chat.id), int(mid))
    except Exception:
        pass

    doc = await _find_exact(photo_uids, photo_file_ids, None, origin, scope)
    if doc:
        return doc, "uid/origin"

    data = await _download(bot, str(getattr(media.obj, "file_id", "") or ""))
    if not data:
        return None, "download_failed"

    hashed = await asyncio.to_thread(
        hash_photo if media.media_type == "photo" else hash_video,
        data,
    )

    doc = await _find_exact(photo_uids, photo_file_ids, hashed.sha256, origin, scope)
    if doc:
        return doc, "exact"

    if media.media_type == "photo":
        doc = await _photo_similarity(hashed, scope)
        if doc:
            return doc, "photo_similarity"

    if media.media_type == "video":
        doc = await _video_similarity(hashed, scope)
        if doc:
            return doc, "video_similarity"

    return None, "not_found"
