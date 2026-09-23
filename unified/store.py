from __future__ import annotations

import logging
from datetime import datetime, timezone
from typing import Any
import re
import unicodedata

from motor.motor_asyncio import AsyncIOMotorClient

from unified.config import settings

log = logging.getLogger(__name__)

client = AsyncIOMotorClient(
    settings.mongo_uri,
    serverSelectionTimeoutMS=5000,
    connectTimeoutMS=5000,
    socketTimeoutMS=15000,
    maxPoolSize=50,
)
db = client[settings.db_name]
characters = db.characters


def _name_key(value: str | None) -> str:
    text = unicodedata.normalize("NFKC", str(value or "")).lower()
    text = re.sub(r"[\\u200b-\\u200f\\u2060\\ufeff]", "", text)
    text = re.sub(r"[^0-9a-z\\u1000-\\u109f\\u3040-\\u30ff\\u4e00-\\u9fff\\uac00-\\ud7af\\s]+", " ", text)
    return re.sub(r"\\s+", " ", text).strip()


def _now():
    return datetime.now(timezone.utc)

def _chunks(value: str | None, count: int = 9) -> list[str]:
    if not value:
        return []
    text = str(value).strip().lower()
    try:
        number = int(text, 16)
    except Exception:
        return []
    bits = len(text) * 4
    if not bits or count > bits:
        return []
    base, extra = divmod(bits, count)
    out, consumed = [], 0
    for i in range(count):
        size = base + (1 if i < extra else 0)
        shift = bits - consumed - size
        out.append(format((number >> shift) & ((1 << size) - 1), "x"))
        consumed += size
    return out

async def ensure_indexes():
    # The collection stays unified. source_key is the first field so Mongo can
    # narrow a lookup to Catch/Bika/Hallow/etc. before similarity work.
    indexes = [
        ([("source_key", 1), ("name_key", 1)], "idx_source_name_key"),
        ([("name_key", 1)], "idx_global_name_key"),
        ([("source_key", 1), ("file_unique_ids", 1)], "idx_source_file_uid"),
        ([("source_key", 1), ("sha256", 1)], "idx_source_sha256"),
        ([("source_key", 1), ("sha256_aliases", 1)], "idx_source_sha256_alias"),
        ([("source_key", 1), ("phash_chunks", 1)], "idx_source_phash_chunk"),
        ([("source_key", 1), ("dhash_chunks", 1)], "idx_source_dhash_chunk"),
        ([("source_key", 1), ("video_signature", 1)], "idx_source_video_signature"),
        ([("source_key", 1), ("duration_bucket", 1)], "idx_source_duration"),
        ([("source_key", 1), ("media_type", 1), ("duration_bucket", 1)], "idx_source_media_duration"),
        ([("source_origin.chat_id", 1), ("source_origin.message_id", 1)], "idx_origin"),
        ([("sha256", 1)], "idx_global_sha256"),
        ([("sha256_aliases", 1)], "idx_global_sha256_alias"),
        ([("file_unique_ids", 1)], "idx_global_file_uid"),
        ([("video_signature", 1)], "idx_global_video_signature"),
        ([("updated_at", -1)], "idx_updated_at"),
    ]
    for keys, name in indexes:
        await characters.create_index(keys, name=name, background=True)

async def save_character(
    *,
    name: str,
    command: str,
    source_key: str,
    media_type: str,
    file_unique_id: str | None,
    media_hash,
    source_origin: tuple[int, int] | None,
    archive: tuple[int, int] | None = None,
):
    now = _now()
    name = str(name or "").strip()
    name_key = _name_key(name)
    if not name_key:
        log.warning("skip character without normalized name")
        return None
    source_key = (source_key or "unknown").strip().lower()
    uid = file_unique_id or ""
    sha = getattr(media_hash, "sha256", None)

    origin_filter = None
    if source_origin:
        origin_filter = {
            "source_origin.chat_id": source_origin[0],
            "source_origin.message_id": source_origin[1],
        }

    key = origin_filter or (
        {"source_key": source_key, "sha256": sha} if sha else None
    )
    if key is None and uid:
        key = {"source_key": source_key, "file_unique_ids": uid}
    if key is None:
        log.warning("skip character without stable identity: %s", name)
        return None

    doc = {
        "name": name,
        "name_key": name_key,
        "command": command or "/name",
        "source_key": source_key,
        "media_type": media_type,
        "file_unique_ids": [uid] if uid else [],
        "sha256": sha,
        "sha256_aliases": [sha] if sha else [],
        "phash": getattr(media_hash, "phash", None),
        "phash_large": getattr(media_hash, "phash_large", None),
        "dhash": getattr(media_hash, "dhash", None),
        "whash": getattr(media_hash, "whash", None),
        "colorhash": getattr(media_hash, "colorhash", None),
        "crop_hash": getattr(media_hash, "crop_hash", None),
        "pixel_sha256": getattr(media_hash, "pixel_sha256", None),
        "frame_hashes": list(getattr(media_hash, "frame_hashes", ()) or ()),
        "video_samples": [
            {
                "position": s.position,
                "frame_index": s.frame_index,
                "phash": s.phash,
                "dhash": s.dhash,
            }
            for s in (getattr(media_hash, "video_samples", ()) or ())
        ],
        "video_signature": getattr(media_hash, "video_signature", None),
        "duration_ms": int(getattr(media_hash, "duration_ms", 0) or 0),
        "duration_bucket": int(round((getattr(media_hash, "duration_ms", 0) or 0) / 1000)),
        "phash_chunks": _chunks(getattr(media_hash, "phash", None)),
        "dhash_chunks": _chunks(getattr(media_hash, "dhash", None)),
        "source_origin": (
            {"chat_id": source_origin[0], "message_id": source_origin[1]}
            if source_origin
            else None
        ),
        "archive": (
            {"chat_id": archive[0], "message_id": archive[1]}
            if archive
            else None
        ),
        "created_at": now,
        "updated_at": now,
    }

    update = {
        "$set": {
            k: v
            for k, v in doc.items()
            if k not in {"file_unique_ids", "sha256_aliases", "created_at"}
        },
        "$setOnInsert": {"created_at": now},
        "$addToSet": {},
    }
    if uid:
        update["$addToSet"]["file_unique_ids"] = uid
    if sha:
        update["$addToSet"]["sha256_aliases"] = sha
    if not update["$addToSet"]:
        update.pop("$addToSet")

    await characters.update_one(key, update, upsert=True)
    return await characters.find_one(key)

async def close():
    client.close()
