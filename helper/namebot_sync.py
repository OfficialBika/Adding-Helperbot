from __future__ import annotations

import asyncio
import logging
from datetime import datetime, timezone
from typing import Any

log = logging.getLogger(__name__)

SERVICE_ID = "namebotv3"
DEFAULT_POLL_SECONDS = 15

_latest: dict[str, Any] = {}


def latest_status() -> dict[str, Any]:
    return dict(_latest)


def _format_status(doc: dict[str, Any]) -> str:
    heartbeat = doc.get("heartbeat_at")
    if isinstance(heartbeat, datetime):
        age = max(0, int((datetime.now(timezone.utc) - heartbeat).total_seconds()))
        heartbeat_text = f"{age}s ago"
    else:
        heartbeat_text = "unknown"
    engine = doc.get("lookup_engine") or (doc.get("lookup_stats") or {}).get("mode") or "unknown"
    version = doc.get("version") or "unknown"
    commit = doc.get("git_commit") or "not-set"
    return f"version={version} commit={commit} engine={engine} heartbeat={heartbeat_text}"


async def monitor_namebot(db, poll_seconds: int = DEFAULT_POLL_SECONDS) -> None:
    """Observe NameBotV3's Mongo service contract and log meaningful changes."""
    global _latest
    poll_seconds = max(5, int(poll_seconds))
    collection = db["service_registry"]

    while True:
        try:
            doc = await collection.find_one({"_id": SERVICE_ID})
            if not doc:
                if _latest.get("status") != "missing":
                    log.warning("NameBotV3 registry entry not found; waiting for NameBot to publish status")
                    _latest = {"status": "missing"}
            else:
                previous = _latest
                _latest = dict(doc)
                signature = (
                    doc.get("version"),
                    doc.get("git_commit"),
                    doc.get("lookup_engine"),
                )
                previous_signature = (
                    previous.get("version"),
                    previous.get("git_commit"),
                    previous.get("lookup_engine"),
                )
                if signature != previous_signature:
                    log.info("NameBotV3 runtime changed: %s", _format_status(doc))
                else:
                    log.debug("NameBotV3 heartbeat: %s", _format_status(doc))
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("NameBotV3 registry monitor failed")
        await asyncio.sleep(poll_seconds)
