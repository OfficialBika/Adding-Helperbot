from __future__ import annotations

import logging
from datetime import datetime, timezone

from unified.store import db

log = logging.getLogger("unified-auth")

authorized_users = db.authorized_users


def _now():
    return datetime.now(timezone.utc)


async def ensure_auth_indexes():
    # MongoDB already provides a unique _id index automatically.
    # Do not recreate it with unique=True; MongoDB rejects additional
    # options on the built-in _id index.
    return


async def is_authorized(user_id: int | None) -> bool:
    if not user_id:
        return False
    return await authorized_users.find_one({"_id": int(user_id)}) is not None


async def grant(user_id: int, granted_by: int):
    user_id = int(user_id)
    await authorized_users.update_one(
        {"_id": user_id},
        {"$set": {"user_id": user_id, "granted_by": int(granted_by), "updated_at": _now()},
         "$setOnInsert": {"created_at": _now()}},
        upsert=True,
    )


async def revoke(user_id: int):
    result = await authorized_users.delete_one({"_id": int(user_id)})
    return result.deleted_count > 0


async def list_authorized():
    return await authorized_users.find(
        {}, {"_id": 0, "user_id": 1, "granted_by": 1, "created_at": 1, "updated_at": 1}
    ).sort("user_id", 1).to_list(length=1000)
