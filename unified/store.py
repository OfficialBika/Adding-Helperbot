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
    text = re.sub(r"[\u200b-\u200f\u2060\ufeff]", "", text)
    text = re.sub(r"[^0-9a-z\u1000-\u109f\u3040-\u30ff\u4e00-\u9fff\uac00-\ud7af\s]+", " ", text)
    return re.sub(r"\s+", " ", text).strip()


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
        ([("source_key", 1), ("character_id", 1)], "uq_source_character_id", {"unique": True, "partialFilterExpression": {"character_id": {"$exists": True}}}),
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
    for entry in indexes:
        keys, name = entry[:2]
        options = entry[2] if len(entry) > 2 else {}
        await characters.create_index(keys, name=name, background=True, **options)

async def save_character(
    *,
    name: str,
    command: str,
    source_key: str,
    character_id: str | None = None,
    media_type: str,
    file_unique_id: str | None,
    file_id: str | None = None,
    file_unique_ids: list[str] | None = None,
    file_ids: list[str] | None = None,
    media_meta: dict[str, Any] | None = None,
    media_hash=None,
    source_origin: tuple[int, int] | None,
    archive: tuple[int, int] | None = None,
):
    """Insert a new media record, update a matching record, or no-op.

    Identity priority is deliberately media-first:
      1. source + SHA-256
      2. source + Telegram file_unique_id
      3. source-origin as a legacy fallback when no stable media identity exists

    This prevents a new forwarded/inline message carrying the same media from
    creating a duplicate just because its source message ID changed.
    """
    now = _now()
    name = str(name or "").strip()
    name_key = _name_key(name)
    if not name_key:
        log.warning("skip character without normalized name")
        return {"status": "skipped", "document": None}

    source_key = (source_key or "unknown").strip().lower()
    character_id = str(character_id).strip() if character_id is not None and str(character_id).strip() else None
    uid = str(file_unique_id or "").strip()
    unique_ids = list(dict.fromkeys(
        str(x).strip() for x in (file_unique_ids or []) if str(x).strip()
    ))
    if uid and uid not in unique_ids:
        unique_ids.append(uid)
    ids = list(dict.fromkeys(
        str(x).strip() for x in (file_ids or []) if str(x).strip()
    ))
    if file_id and str(file_id).strip() and str(file_id).strip() not in ids:
        ids.append(str(file_id).strip())
    sha = getattr(media_hash, "sha256", None) if media_hash is not None else None

    # Source character ID is the primary identity. A source guarantees that
    # one character ID refers to one character, so a changed media payload or
    # renamed character must update that same record instead of creating one.
    # Media identity remains the fallback for formats without an ID.
    if character_id:
        key = {"source_key": source_key, "character_id": character_id}
    elif sha:
        key = {"source_key": source_key, "sha256": sha}
    elif uid:
        key = {"source_key": source_key, "file_unique_ids": uid}
    elif source_origin:
        key = {
            "source_origin.chat_id": source_origin[0],
            "source_origin.message_id": source_origin[1],
        }
    else:
        log.warning("skip character without stable identity: %s", name)
        return {"status": "skipped", "document": None}

    media_fields = {
        "name": name,
        "name_key": name_key,
        "command": command or "/name",
        "source_key": source_key,
        "character_id": character_id,
        "media_type": media_type,
        "telegram_file_id": str(file_id or ""),
        "telegram_file_unique_id": uid,
        "file_ids": ids,
        "file_unique_ids": unique_ids,
        "media_meta": dict(media_meta or {}),
        "sha256": sha,
        "phash": getattr(media_hash, "phash", None) if media_hash is not None else None,
        "phash_large": getattr(media_hash, "phash_large", None) if media_hash is not None else None,
        "dhash": getattr(media_hash, "dhash", None) if media_hash is not None else None,
        "whash": getattr(media_hash, "whash", None) if media_hash is not None else None,
        "colorhash": getattr(media_hash, "colorhash", None) if media_hash is not None else None,
        "crop_hash": getattr(media_hash, "crop_hash", None) if media_hash is not None else None,
        "pixel_sha256": getattr(media_hash, "pixel_sha256", None) if media_hash is not None else None,
        "frame_hashes": list(getattr(media_hash, "frame_hashes", ()) or ()) if media_hash is not None else [],
        "video_samples": [
            {
                "position": s.position,
                "frame_index": s.frame_index,
                "phash": s.phash,
                "dhash": s.dhash,
            }
            for s in (getattr(media_hash, "video_samples", ()) or ()) if media_hash is not None
        ],
        "video_signature": getattr(media_hash, "video_signature", None) if media_hash is not None else None,
        "duration_ms": int(getattr(media_hash, "duration_ms", 0) or 0) if media_hash is not None else 0,
        "duration_bucket": int(round((getattr(media_hash, "duration_ms", 0) or 0) / 1000)) if media_hash is not None else 0,
        "phash_chunks": _chunks(getattr(media_hash, "phash", None)) if media_hash is not None else [],
        "dhash_chunks": _chunks(getattr(media_hash, "dhash", None)) if media_hash is not None else [],
    }
    if character_id is None:
        media_fields.pop("character_id", None)

    existing = await characters.find_one(key)
    if existing is None:
        doc = dict(media_fields)
        doc["file_ids"] = ids
        doc["file_unique_ids"] = unique_ids
        doc["sha256_aliases"] = [sha] if sha else []
        doc["source_origin"] = (
            {"chat_id": source_origin[0], "message_id": source_origin[1]}
            if source_origin
            else None
        )
        doc["archive"] = (
            {"chat_id": archive[0], "message_id": archive[1]}
            if archive
            else None
        )
        doc["created_at"] = now
        doc["updated_at"] = now
        await characters.insert_one(doc)
        return {"status": "saved", "document": await characters.find_one(key)}

    # Do not touch updated_at for an exact repeat. Only write fields that
    # genuinely changed, so MongoDB can report a true no-op.
    changed = {}
    for field, value in media_fields.items():
        if existing.get(field) != value:
            changed[field] = value

    # New Telegram file IDs/content aliases are useful lookup identities and
    # should be merged without replacing the existing values.
    old_ids = set(existing.get("file_ids") or [])
    new_ids = [x for x in ids if x not in old_ids]
    if new_ids:
        changed["file_ids"] = {"$each": new_ids}

    old_uids = set(existing.get("file_unique_ids") or [])
    new_unique_ids = [x for x in unique_ids if x not in old_uids]
    if new_unique_ids:
        changed["file_unique_ids"] = {"$each": new_unique_ids}

    old_aliases = set(existing.get("sha256_aliases") or [])
    if sha and sha not in old_aliases:
        changed["sha256_aliases"] = {"$each": [sha]}

    update = {}
    set_fields = {
        k: v for k, v in changed.items()
        if k not in {"file_ids", "file_unique_ids", "sha256_aliases"}
    }
    if set_fields:
        update["$set"] = set_fields
    if "file_ids" in changed or "file_unique_ids" in changed or "sha256_aliases" in changed:
        update["$addToSet"] = {}
        if "file_ids" in changed:
            update["$addToSet"]["file_ids"] = {"$each": new_ids}
        if "file_unique_ids" in changed:
            update["$addToSet"]["file_unique_ids"] = {"$each": new_unique_ids}
        if "sha256_aliases" in changed:
            update["$addToSet"]["sha256_aliases"] = {"$each": [sha]}

    if not update:
        return {"status": "unchanged", "document": existing}

    update.setdefault("$set", {})["updated_at"] = now
    await characters.update_one({"_id": existing["_id"]}, update)
    return {"status": "updated", "document": await characters.find_one({"_id": existing["_id"]})}

async def close():
    client.close()
