from __future__ import annotations

import asyncio
import io
import logging

from aiogram import Bot
from aiogram.types import Message

from unified.config import settings
from unified.store import characters, _chunks
from services.hash_service import hash_photo, hash_video, hamming_hex
from services.source_resolver import resolve_lookup_scope, output_command_from_message
from utils.media import extract_media

log = logging.getLogger(__name__)

def _scope(message: Message) -> list[str] | None:
    scope = resolve_lookup_scope(message)
    return scope.collections

async def _download(bot: Bot, file_id: str) -> bytes | None:
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

async def _find_exact(file_uid: str, sha: str | None, origin, scope):
    ors = []
    if file_uid: ors.append({"file_unique_ids": file_uid})
    if sha: ors.extend([{"sha256": sha}, {"sha256_aliases": sha}])
    if origin:
        ors.append({"source_origin.chat_id": origin[0], "source_origin.message_id": origin[1]})
    if not ors:
        return None
    query = {"$or": ors}
    if scope:
        query["source_key"] = {"$in": scope}
    return await characters.find_one(query)

def _similarity(query_hash, item) -> float:
    metrics = []
    for a, b, weight in (
        (query_hash.phash, item.get("phash"), .35),
        (query_hash.dhash, item.get("dhash"), .25),
        (query_hash.whash, item.get("whash"), .15),
        (query_hash.phash_large, item.get("phash_large"), .15),
        (query_hash.colorhash, item.get("colorhash"), .10),
    ):
        distance = hamming_hex(a, b)
        if distance is not None:
            bits = max(1, len(str(a)) * 4)
            metrics.append((max(0.0, 1.0 - distance / bits), weight))
    return sum(score * weight for score, weight in metrics) / sum(weight for _, weight in metrics) if metrics else 0.0

async def lookup_message(bot: Bot, message: Message):
    media = extract_media(message)
    if not media:
        return None, "no_media"

    source_message = media.source_message
    scope = _scope(source_message)
    uid = str(getattr(media.obj, "file_unique_id", "") or "")

    origin = None
    try:
        origin_obj = getattr(source_message, "forward_origin", None)
        chat = getattr(origin_obj, "chat", None) or getattr(origin_obj, "sender_chat", None)
        mid = getattr(origin_obj, "message_id", None)
        if chat and mid is not None:
            origin = (int(chat.id), int(mid))
    except Exception:
        pass

    doc = await _find_exact(uid, None, origin, scope)
    if doc:
        return doc, "uid/origin"

    data = await _download(bot, str(getattr(media.obj, "file_id", "") or ""))
    if not data:
        return None, "download_failed"

    hashed = await asyncio.to_thread(
        hash_photo if media.media_type == "photo" else hash_video,
        data,
    )
    doc = await _find_exact(uid, hashed.sha256, origin, scope)
    if doc:
        return doc, "exact"

    if media.media_type == "photo" and hashed.phash:
        chunk_values = set(_chunks(hashed.phash)) | set(_chunks(hashed.dhash))
        if chunk_values:
            query = {
                "$or": [
                    {"phash_chunks": {"$in": list(chunk_values)}},
                    {"dhash_chunks": {"$in": list(chunk_values)}},
                ]
            }
            if scope:
                query["source_key"] = {"$in": scope}
            cursor = characters.find(query).limit(2500)
            best = None
            best_score = 0.0
            async for item in cursor:
                score = _similarity(hashed, item)
                p = hamming_hex(hashed.phash, item.get("phash"))
                d = hamming_hex(hashed.dhash, item.get("dhash"))
                if ((p is not None and p <= settings.photo_threshold) or
                    (d is not None and d <= settings.dhash_threshold)) and score >= 0.80:
                    if score > best_score:
                        best, best_score = item, score
            if best:
                return best, "photo_similarity"

    if media.media_type == "video":
        if hashed.video_signature:
            query = {"video_signature": hashed.video_signature}
            if scope:
                query["source_key"] = {"$in": scope}
            doc = await characters.find_one(query)
            if doc:
                return doc, "video_signature"

        if hashed.duration_ms:
            second = round(hashed.duration_ms / 1000)
            query = {
                "media_type": "video",
                "duration_bucket": {"$gte": max(0, second - 4), "$lte": second + 4},
            }
            if scope:
                query["source_key"] = {"$in": scope}
            cursor = characters.find(query).limit(5000)
            best = None
            best_avg = float("inf")
            async for item in cursor:
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
            if best:
                return best, "video_similarity"

    return None, "not_found"
