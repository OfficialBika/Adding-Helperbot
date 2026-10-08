from __future__ import annotations

import logging
import re
import unicodedata
from datetime import datetime, timezone
from typing import Any

from motor.motor_asyncio import AsyncIOMotorClient

from unified.config import settings

log = logging.getLogger("unified-store")

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


def _index_source_variant(source_key: str, source_variant: str | None, *, file_unique_id: str | None = None, source_origin: tuple[int, int] | None = None) -> str | None:
    if source_key != "items_grabber_fw":
        return source_variant
    if source_variant:
        return source_variant
    if file_unique_id:
        return f"unknown_uid:{file_unique_id}"
    if source_origin:
        return f"unknown_origin:{source_origin[0]}:{source_origin[1]}"
    return "unknown_record"


def _identity_key(source_key: str, character_id: str | None, source_variant: str | None, uid: str | None, origin: tuple[int, int] | None):
    if source_key in {"items_characters_hallow", "items_character_catcher_fw"}:
        if uid:
            return {"source_key": source_key, "file_unique_ids": uid}
        if origin:
            return {"source_key": source_key, "source_origin.chat_id": origin[0], "source_origin.message_id": origin[1]}
        return None
    if source_key == "items_grabber_fw":
        if source_variant and character_id:
            return {"source_key": source_key, "source_variant": source_variant, "character_id": character_id}
        if uid:
            return {"source_key": source_key, "file_unique_ids": uid}
        if origin:
            return {"source_key": source_key, "source_origin.chat_id": origin[0], "source_origin.message_id": origin[1]}
        return None
    if character_id:
        return {"source_key": source_key, "character_id": character_id}
    if uid:
        return {"source_key": source_key, "file_unique_ids": uid}
    if origin:
        return {"source_key": source_key, "source_origin.chat_id": origin[0], "source_origin.message_id": origin[1]}
    return None


async def ensure_indexes():
    required = [
        ([("source_key", 1), ("name_key", 1)], "idx_source_name_key"),
        (
            [("source_key", 1), ("source_variant", 1), ("character_id", 1)],
            "uq_source_variant_character_id",
            {"unique": True, "partialFilterExpression": {"character_id": {"$exists": True}}},
        ),
        ([("source_key", 1), ("file_ids", 1)], "idx_source_file_id"),
        ([("source_key", 1), ("file_unique_ids", 1)], "idx_source_file_uid"),
        ([("source_key", 1), ("source_origin.chat_id", 1), ("source_origin.message_id", 1)], "idx_source_origin"),
        ([("updated_at", -1)], "idx_updated_at"),
    ]
    obsolete = {
        "idx_global_name_key", "idx_source_telegram_file_uid", "idx_global_telegram_file_uid",
        "idx_global_telegram_file_id", "idx_global_file_id", "idx_source_sha256",
        "idx_source_sha256_alias", "idx_source_phash_chunk", "idx_source_dhash_chunk",
        "idx_global_phash_chunk", "idx_global_dhash_chunk", "idx_source_video_signature",
        "idx_source_duration", "idx_source_media_duration", "idx_global_sha256",
        "idx_global_sha256_alias", "idx_global_file_uid", "idx_legacy_file_uid",
        "idx_legacy_photo_file_uid", "idx_legacy_video_file_uid", "idx_legacy_media_file_uid",
        "idx_global_video_signature", "uq_source_character_id",
        "uq_grabber_source_variant_character_id",
    }
    try:
        existing_indexes = {
            str(item["name"])
            async for item in characters.list_indexes()
            if item.get("name")
        }
    except Exception:
        existing_indexes = set()

    for name in obsolete & existing_indexes:
        try:
            await characters.drop_index(name)
        except Exception:
            log.warning("failed to drop obsolete index name=%s", name)

    for entry in required:
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
    source_origin: tuple[int, int] | None = None,
    source_variant: str | None = None,
    source_signature: str | None = None,
    archive: tuple[int, int] | None = None,
):
    name = str(name or "").strip()
    source_key = str(source_key or "").strip().lower()
    command = str(command or "/name").strip() or "/name"
    media_type = str(media_type or "unknown").strip().lower()
    if not name or not source_key:
        return {"status": "skipped", "document": None, "reason": "missing_name_or_source"}

    character_id = str(character_id).strip() if character_id is not None and str(character_id).strip() else None
    source_variant = str(source_variant or "").strip().lower() or None
    source_signature = str(source_signature or "").strip() or None
    if source_key in {"items_characters_hallow", "items_character_catcher_fw"}:
        character_id = None

    uid = str(file_unique_id or "").strip()
    unique_ids = list(dict.fromkeys(str(x).strip() for x in (file_unique_ids or []) if str(x).strip()))
    if uid and uid not in unique_ids:
        unique_ids.insert(0, uid)
    ids = list(dict.fromkeys(str(x).strip() for x in (file_ids or []) if str(x).strip()))
    if file_id and str(file_id).strip() and str(file_id).strip() not in ids:
        ids.append(str(file_id).strip())

    if media_type != "metadata" and not unique_ids:
        return {"status": "skipped", "document": None, "reason": "missing_file_unique_id"}

    indexed_variant = _index_source_variant(source_key, source_variant, file_unique_id=uid, source_origin=source_origin)
    identity = _identity_key(
        source_key,
        character_id,
        indexed_variant if source_key == "items_grabber_fw" else source_variant,
        uid,
        source_origin,
    )
    if identity is None:
        return {"status": "skipped", "document": None, "reason": "missing_identity"}

    now = _now()
    fields: dict[str, Any] = {
        "name": name,
        "name_key": _name_key(name),
        "command": command,
        "source_key": source_key,
        "media_type": media_type,
        "telegram_file_id": str(file_id or ""),
        "telegram_file_unique_id": uid,
        "file_ids": ids,
        "file_unique_ids": unique_ids,
        "media_meta": dict(media_meta or {}),
    }
    if character_id is not None:
        fields["character_id"] = character_id
    if source_key == "items_grabber_fw":
        fields["source_variant"] = indexed_variant
        if source_signature:
            fields["source_signature"] = source_signature
    if source_origin is not None:
        fields["source_origin"] = {"chat_id": int(source_origin[0]), "message_id": int(source_origin[1])}
    if archive is not None:
        fields["archive"] = {"chat_id": int(archive[0]), "message_id": int(archive[1])}

    existing = await characters.find_one(identity)
    if existing is None:
        doc = dict(fields)
        doc["created_at"] = now
        doc["updated_at"] = now
        await characters.insert_one(doc)
        saved = await characters.find_one(identity)
        return {"status": "saved", "document": saved or doc, "changes": ["new character record"]}

    set_fields: dict[str, Any] = {}
    for key, value in fields.items():
        if key not in {"file_ids", "file_unique_ids"} and existing.get(key) != value:
            set_fields[key] = value

    old_ids = set(existing.get("file_ids") or [])
    old_uids = set(existing.get("file_unique_ids") or [])
    new_ids = [x for x in ids if x not in old_ids]
    new_uids = [x for x in unique_ids if x not in old_uids]

    update: dict[str, Any] = {}
    if set_fields:
        update["$set"] = set_fields
    if new_ids or new_uids:
        add: dict[str, Any] = {}
        if new_ids:
            add["file_ids"] = {"$each": new_ids}
        if new_uids:
            add["file_unique_ids"] = {"$each": new_uids}
        update["$addToSet"] = add

    if not update:
        return {"status": "unchanged", "document": existing, "changes": []}

    update.setdefault("$set", {})["updated_at"] = now
    await characters.update_one({"_id": existing["_id"]}, update)
    updated = await characters.find_one(identity)

    changes = [f"{key}: changed" for key in set_fields]
    if new_ids:
        changes.append(f"file_ids: +{len(new_ids)}")
    if new_uids:
        changes.append(f"file_unique_ids: +{len(new_uids)}")
    return {"status": "updated", "document": updated or existing, "changes": changes}


async def close():
    client.close()
