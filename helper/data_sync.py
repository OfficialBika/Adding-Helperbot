from __future__ import annotations

import logging
from datetime import datetime, timezone
from typing import Any

from bson import ObjectId

log = logging.getLogger(__name__)

STATE_ID = "adding_bot_items"
STATE_COLLECTION = "data_sync_state"
EVENT_COLLECTION = "data_sync_events"


async def record_change(
    db,
    *,
    operation: str,
    collection: str,
    document_id: Any,
    source_key: str | None = None,
) -> None:
    """Publish a durable MongoDB-backed change signal after an item write.

    The item collection remains the source of truth. This signal is only a
    notification/watermark so NameBot V3 can refresh its secondary indexes
    quickly. Failures here must never break a successful Adding Bot write.
    """
    try:
        now = datetime.now(timezone.utc)
        state = await db[STATE_COLLECTION].find_one_and_update(
            {"_id": STATE_ID},
            {
                "$inc": {"version": 1},
                "$set": {"updated_at": now, "producer": "adding-helperbot"},
                "$setOnInsert": {"created_at": now},
            },
            upsert=True,
            return_document=True,
        )
        version = int((state or {}).get("version", 0))

        event = {
            "version": version,
            "producer": "adding-helperbot",
            "operation": operation,
            "collection": collection,
            "document_id": str(document_id),
            "source_key": source_key or "",
            "created_at": now,
        }
        await db[EVENT_COLLECTION].insert_one(event)
    except Exception:
        log.exception(
            "Failed to publish NameBot data-sync signal operation=%s collection=%s id=%s",
            operation,
            collection,
            document_id,
        )


async def ensure_sync_indexes(db) -> None:
    """Create lightweight indexes for the cross-service sync contract."""
    try:
        await db[STATE_COLLECTION].create_index("updated_at")
        await db[EVENT_COLLECTION].create_index([("version", 1)], unique=True)
        await db[EVENT_COLLECTION].create_index("created_at", expireAfterSeconds=604800)
    except Exception:
        log.exception("Failed to create data-sync indexes")
