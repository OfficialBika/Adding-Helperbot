from __future__ import annotations

import logging
from datetime import datetime, timezone
from typing import Any
import re
import unicodedata

from motor.motor_asyncio import AsyncIOMotorClient
from pymongo.errors import DuplicateKeyError

from unified.config import settings
from unified.uid_index import upsert_document

log = logging.getLogger(__name__)

client = AsyncIOMotorClient(
    settings.mongo_uri,
    serverSelectionTimeoutMS=settings.mongo_server_selection_timeout_ms,
    connectTimeoutMS=settings.mongo_connect_timeout_ms,
    socketTimeoutMS=settings.mongo_socket_timeout_ms,
    minPoolSize=settings.mongo_min_pool_size,
    maxPoolSize=settings.mongo_max_pool_size,
    maxIdleTimeMS=settings.mongo_max_idle_time_ms,
    retryWrites=True,
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


def _index_source_variant(
    source_key: str,
    source_variant: str | None,
    *,
    file_unique_id: str | None = None,
    sha256: str | None = None,
    source_origin: tuple[int, int] | None = None,
) -> str | None:
    """Return the discriminator used by the source/ID unique index.

    Known Grabber FW variants remain stable. Unknown Grabber FW records are
    scoped to their exact media identity so a numeric character ID never
    becomes their upsert identity.
    """
    if source_key != "items_grabber_fw":
        return source_variant
    if source_variant:
        return source_variant
    if file_unique_id:
        return f"unknown_uid:{file_unique_id}"
    if sha256:
        return f"unknown_sha256:{sha256}"
    if source_origin:
        return f"unknown_origin:{source_origin[0]}:{source_origin[1]}"
    return "unknown_record"


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
    indexes = [
        ([("source_key", 1), ("name_key", 1)], "idx_source_name_key"),
        (
            [("source_key", 1), ("source_variant", 1), ("character_id", 1)],
            "uq_source_variant_character_id",
            {
                "unique": True,
                "partialFilterExpression": {"character_id": {"$exists": True}},
            },
        ),
        ([("name_key", 1)], "idx_global_name_key"),
        ([("source_key", 1), ("file_ids", 1)], "idx_source_file_id"),
        ([("source_key", 1), ("file_unique_ids", 1)], "idx_source_file_uid"),
        ([("source_key", 1), ("telegram_file_unique_id", 1)], "idx_source_telegram_file_uid"),
        ([("telegram_file_unique_id", 1)], "idx_global_telegram_file_uid"),
        ([("telegram_file_id", 1)], "idx_global_telegram_file_id"),
        ([("file_ids", 1)], "idx_global_file_id"),
        ([("source_key", 1), ("sha256", 1)], "idx_source_sha256"),
        ([("source_key", 1), ("sha256_aliases", 1)], "idx_source_sha256_alias"),
        ([("source_key", 1), ("phash_chunks", 1)], "idx_source_phash_chunk"),
        ([("source_key", 1), ("dhash_chunks", 1)], "idx_source_dhash_chunk"),
        ([("phash_chunks", 1)], "idx_global_phash_chunk"),
        ([("dhash_chunks", 1)], "idx_global_dhash_chunk"),
        ([("source_key", 1), ("video_signature", 1)], "idx_source_video_signature"),
        ([("source_key", 1), ("duration_bucket", 1)], "idx_source_duration"),
        ([("source_key", 1), ("media_type", 1), ("duration_bucket", 1)], "idx_source_media_duration"),
        ([("source_origin.chat_id", 1), ("source_origin.message_id", 1)], "idx_origin"),
        ([("sha256", 1)], "idx_global_sha256"),
        ([("sha256_aliases", 1)], "idx_global_sha256_alias"),
        ([("file_unique_ids", 1)], "idx_global_file_uid"),
        ([("file_unique_id", 1)], "idx_legacy_file_uid"),
        ([("photo_file_unique_id", 1)], "idx_legacy_photo_file_uid"),
        ([("video_file_unique_id", 1)], "idx_legacy_video_file_uid"),
        ([("media.file_unique_id", 1)], "idx_legacy_media_file_uid"),
        ([("video_signature", 1)], "idx_global_video_signature"),
        ([("updated_at", -1)], "idx_updated_at"),
    ]
    for legacy_name in ("uq_source_character_id", "uq_grabber_source_variant_character_id"):
        try:
            await characters.drop_index(legacy_name)
        except Exception:
            pass
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
    source_origin: tuple[int, int] | None = None,
    source_variant: str | None = None,
    source_signature: str | None = None,
    archive: tuple[int, int] | None = None,
):
    """Insert/update a record while preserving existing identity semantics."""
    now = _now()
    name = str(name or "").strip()
    name_key = _name_key(name)
    if not name_key:
        log.warning("skip character without normalized name")
        return {"status": "skipped", "document": None}

    source_key = (source_key or "unknown").strip().lower()
    character_id = str(character_id).strip() if character_id is not None and str(character_id).strip() else None
    source_variant = str(source_variant or "").strip().lower() or None
    source_signature = str(source_signature or "").strip() or None
    if source_key == "items_characters_hallow":
        character_id = None

    if media_type != "metadata" and not str(file_unique_id or "").strip() and not any(
        str(x).strip() for x in (file_unique_ids or []) if x is not None
    ):
        log.error("reject media without file_unique_id source=%s name=%s type=%s", source_key, name, media_type)
        return {"status": "skipped", "document": None, "reason": "missing_file_unique_id"}

    uid = str(file_unique_id or "").strip()
    unique_ids = list(dict.fromkeys(
        str(x).strip() for x in (file_unique_ids or []) if str(x).strip()
    ))
    if uid and uid not in unique_ids:
        unique_ids.insert(0, uid)
    elif not uid and unique_ids:
        uid = unique_ids[0]
    ids = list(dict.fromkeys(
        str(x).strip() for x in (file_ids or []) if str(x).strip()
    ))
    if file_id and str(file_id).strip() and str(file_id).strip() not in ids:
        ids.append(str(file_id).strip())
    sha = getattr(media_hash, "sha256", None) if media_hash is not None else None

    if source_key == "items_characters_hallow":
        if uid:
            key = {"source_key": source_key, "file_unique_ids": uid}
        elif sha:
            key = {"source_key": source_key, "sha256": sha}
        elif character_id:
            key = {"source_key": source_key, "character_id": character_id}
        elif source_origin:
            key = {"source_origin.chat_id": source_origin[0], "source_origin.message_id": source_origin[1]}
        else:
            key = None
    elif source_key == "items_grabber_fw":
        if source_variant and character_id:
            key = {"source_key": source_key, "source_variant": source_variant, "character_id": character_id}
        elif uid:
            key = {"source_key": source_key, "file_unique_ids": uid}
        elif sha:
            key = {"source_key": source_key, "sha256": sha}
        elif source_origin:
            key = {"source_origin.chat_id": source_origin[0], "source_origin.message_id": source_origin[1]}
        else:
            key = None
    elif character_id:
        key = {"source_key": source_key, "character_id": character_id}
    elif sha:
        key = {"source_key": source_key, "sha256": sha}
    elif uid:
        key = {"source_key": source_key, "file_unique_ids": uid}
    elif source_origin:
        key = {"source_origin.chat_id": source_origin[0], "source_origin.message_id": source_origin[1]}
    else:
        log.warning("skip character without stable identity: %s", name)
        return {"status": "skipped", "document": None}

    media_hash_fields = {
        "sha256", "phash", "phash_large", "dhash", "whash", "colorhash",
        "crop_hash", "pixel_sha256", "frame_hashes", "video_samples",
        "video_signature", "duration_ms", "duration_bucket",
        "phash_chunks", "dhash_chunks",
    }

    media_fields = {
        "name": name,
        "name_key": name_key,
        "command": command or "/name",
        "source_key": source_key,
        "character_id": character_id,
        "media_type": media_type,
        "media_meta": dict(media_meta or {}),
    }
    if media_type != "metadata":
        media_fields.update({
            "telegram_file_id": str(file_id or ""),
            "telegram_file_unique_id": uid,
            "file_ids": ids,
            "file_unique_ids": unique_ids,
        })
    elif uid or ids:
        media_fields.update({
            "telegram_file_id": str(file_id or ""),
            "telegram_file_unique_id": uid,
            "file_ids": ids,
            "file_unique_ids": unique_ids,
        })

    if media_hash is not None:
        media_fields.update({
            "sha256": sha,
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
        })

    if source_key == "items_grabber_fw":
        indexed_variant = _index_source_variant(
            source_key,
            source_variant,
            file_unique_id=uid,
            sha256=sha,
            source_origin=source_origin,
        )
        if indexed_variant:
            media_fields["source_variant"] = indexed_variant
        if source_signature:
            media_fields["source_signature"] = source_signature

    async def _merge_update(existing: dict) -> dict:
        changed = {}
        for field, value in media_fields.items():
            # Never downgrade a known media/identity field with empty values when
            # this observation is metadata-only or when download failed.
            if field in {"telegram_file_id", "telegram_file_unique_id"} and not value:
                continue
            if field in media_hash_fields and media_hash is None:
                continue
            if existing.get(field) != value:
                changed[field] = value

        old_ids = set(existing.get("file_ids") or [])
        new_ids = [x for x in ids if x not in old_ids]
        old_uids = set(existing.get("file_unique_ids") or [])
        new_unique_ids = [x for x in unique_ids if x not in old_uids]
        old_aliases = set(existing.get("sha256_aliases") or [])

        update = {}
        set_fields = {
            k: v for k, v in changed.items()
            if k not in {"file_ids", "file_unique_ids", "sha256_aliases"}
        }
        if set_fields:
            update["$set"] = set_fields
        if new_ids or new_unique_ids or (sha and sha not in old_aliases):
            update["$addToSet"] = {}
            if new_ids:
                update["$addToSet"]["file_ids"] = {"$each": new_ids}
            if new_unique_ids:
                update["$addToSet"]["file_unique_ids"] = {"$each": new_unique_ids}
            if sha and sha not in old_aliases:
                update["$addToSet"]["sha256_aliases"] = {"$each": [sha]}

        if not update:
            await upsert_document(existing)
            return {"status": "unchanged", "document": existing, "changes": []}

        changed_fields = []
        for field in set_fields:
            if field == "updated_at":
                continue
            old_value = existing.get(field)
            new_value = set_fields[field]
            if field == "media_meta":
                old_meta = old_value or {}
                new_meta = new_value or {}
                for meta_key in sorted(set(old_meta) | set(new_meta)):
                    if old_meta.get(meta_key) != new_meta.get(meta_key):
                        changed_fields.append(
                            f"media_meta.{meta_key}: {old_meta.get(meta_key)!r} -> {new_meta.get(meta_key)!r}"
                        )
            elif field in {"sha256", "phash", "phash_large", "dhash", "whash", "colorhash", "crop_hash", "pixel_sha256", "video_signature"}:
                changed_fields.append(f"{field}: changed")
            elif field in {"name", "command", "media_type", "character_id", "name_key"}:
                changed_fields.append(f"{field}: {old_value!r} -> {new_value!r}")
            else:
                changed_fields.append(f"{field}: changed")

        if new_ids:
            changed_fields.append(f"file_ids: +{len(new_ids)}")
        if new_unique_ids:
            changed_fields.append(f"file_unique_ids: +{len(new_unique_ids)}")
        if sha and sha not in old_aliases:
            changed_fields.append("sha256_aliases: +1")

        update.setdefault("$set", {})["updated_at"] = now
        try:
            await characters.update_one({"_id": existing["_id"]}, update)
        except DuplicateKeyError:
            # Another writer won the same identity race; re-read and merge into
            # that winner rather than leaking a duplicate or turning a harmless
            # concurrent ingest into an error.
            winner = await characters.find_one(key)
            if winner is None:
                raise
            return await _merge_update(winner)

        updated_doc = await characters.find_one({"_id": existing["_id"]})
        await upsert_document(updated_doc)

        from unified.lookup_cache import positive_uid_cache
        positive_uid_cache.invalidate(
            list(dict.fromkeys([*old_uids, *unique_ids])),
            source_key,
        )
        return {"status": "updated", "document": updated_doc, "changes": changed_fields}

    existing = await characters.find_one(key)
    if existing is None:
        doc = dict(media_fields)
        if media_type != "metadata":
            doc["file_ids"] = ids
            doc["file_unique_ids"] = unique_ids
        else:
            doc.setdefault("file_ids", ids)
            doc.setdefault("file_unique_ids", unique_ids)
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
        try:
            await characters.insert_one(doc)
        except DuplicateKeyError:
            # A concurrent writer inserted the same unique source/ID record.
            # Merge this observation into the winner instead of failing.
            existing = await characters.find_one(key)
            if existing is None:
                raise
            return await _merge_update(existing)

        saved_doc = await characters.find_one(key)
        await upsert_document(saved_doc)
        return {"status": "saved", "document": saved_doc, "changes": ["new character record"]}

    return await _merge_update(existing)


async def close():
    client.close()
