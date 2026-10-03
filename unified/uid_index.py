from __future__ import annotations

import asyncio
import logging
import sqlite3
from collections.abc import Iterable
from pathlib import Path
from threading import RLock, local
from typing import Any

from unified.config import settings

log = logging.getLogger(__name__)

_SCHEMA_VERSION = 2
_LOCAL = local()
_HOT_LOCK = RLock()
_HOT_SOURCE: dict[tuple[str, str], dict[str, Any]] = {}
# Per-UID source bookkeeping keeps global uniqueness updates O(number of sources
# for that UID) instead of scanning the entire RAM hot index on every upsert.
_HOT_UID_SOURCES: dict[str, dict[str, dict[str, Any]]] = {}
_HOT_GLOBAL: dict[str, dict[str, Any] | None] = {}


def _path() -> str:
    path = Path(settings.uid_index_path)
    if not path.is_absolute():
        path = Path(__file__).resolve().parents[1] / path
    path.parent.mkdir(parents=True, exist_ok=True)
    return str(path)


def _connect() -> sqlite3.Connection:
    conn = getattr(_LOCAL, "conn", None)
    if conn is not None:
        try:
            conn.execute("SELECT 1")
            return conn
        except sqlite3.Error:
            _LOCAL.conn = None
    conn = sqlite3.connect(_path(), timeout=5.0)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("PRAGMA busy_timeout=5000")
    _LOCAL.conn = conn
    return conn


def _init_sync() -> None:
    conn = _connect()
    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS meta (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL
        )
        """
    )
    conn.execute(
        """
        CREATE TABLE IF NOT EXISTS uid_index (
            source_key TEXT NOT NULL,
            uid TEXT NOT NULL,
            name TEXT NOT NULL,
            command TEXT NOT NULL,
            media_type TEXT NOT NULL,
            updated_at TEXT,
            PRIMARY KEY (source_key, uid)
        )
        """
    )
    conn.execute("CREATE INDEX IF NOT EXISTS idx_uid_index_uid ON uid_index(uid)")
    conn.execute(
        "CREATE INDEX IF NOT EXISTS idx_uid_index_source_uid ON uid_index(source_key, uid)"
    )
    conn.execute(
        """
        INSERT INTO meta(key, value) VALUES('schema_version', ?)
        ON CONFLICT(key) DO UPDATE SET value=excluded.value
        """,
        (str(_SCHEMA_VERSION),),
    )
    conn.commit()


def _load_hot_sync() -> int:
    conn = _connect()
    rows = conn.execute(
        "SELECT source_key, uid, name, command, media_type FROM uid_index"
    ).fetchall()
    source_hot: dict[tuple[str, str], dict[str, Any]] = {}
    uid_sources: dict[str, dict[str, dict[str, Any]]] = {}
    global_hot: dict[str, dict[str, Any] | None] = {}
    for row in rows:
        record = dict(row)
        source = str(record.get("source_key") or "").strip().lower()
        uid = str(record.get("uid") or "").strip()
        if not source or not uid:
            continue
        source_hot[(source, uid)] = record
        uid_sources.setdefault(uid, {})[source] = record

    for uid, sources in uid_sources.items():
        global_hot[uid] = next(iter(sources.values())) if len(sources) == 1 else None

    with _HOT_LOCK:
        _HOT_SOURCE.clear()
        _HOT_SOURCE.update(source_hot)
        _HOT_UID_SOURCES.clear()
        _HOT_UID_SOURCES.update(uid_sources)
        _HOT_GLOBAL.clear()
        _HOT_GLOBAL.update(global_hot)
    return len(source_hot)


async def ensure_uid_index() -> None:
    await asyncio.to_thread(_init_sync)
    count = await asyncio.to_thread(_load_hot_sync)
    log.info("UID RAM hot index loaded entries=%s", count)


def lookup_hot_source(source_keys: list[str], uids: list[str]) -> dict[str, Any] | None:
    if not source_keys or not uids:
        return None
    with _HOT_LOCK:
        for source in source_keys:
            normalized = str(source).strip().lower()
            for uid in uids:
                record = _HOT_SOURCE.get((normalized, str(uid).strip()))
                if record:
                    return dict(record)
    return None


def lookup_hot_global(uids: list[str], limit: int = 2) -> list[dict[str, Any]]:
    if not uids:
        return []
    results: list[dict[str, Any]] = []
    with _HOT_LOCK:
        for uid in uids:
            record = _HOT_GLOBAL.get(str(uid).strip())
            if record is not None:
                results.append(dict(record))
            if len(results) >= max(1, int(limit)):
                break
    return results


def _lookup_source_sync(source_keys: list[str], uids: list[str]) -> dict[str, Any] | None:
    if not source_keys or not uids:
        return None
    conn = _connect()
    placeholders_u = ",".join("?" for _ in uids)

    # Respect caller source priority. In particular, Catch lookups pass
    # items_character_catcher before items_character_catcher_fw, and the same
    # UID is allowed to exist in both source namespaces.
    for source in source_keys:
        normalized = str(source or "").strip().lower()
        if not normalized:
            continue
        row = conn.execute(
            f"""
            SELECT source_key, uid, name, command, media_type
            FROM uid_index
            WHERE source_key = ?
              AND uid IN ({placeholders_u})
            ORDER BY rowid DESC
            LIMIT 1
            """,
            [normalized, *uids],
        ).fetchone()
        if row:
            return dict(row)
    return None


async def lookup_source(source_keys: list[str], uids: list[str]) -> dict[str, Any] | None:
    return await asyncio.to_thread(_lookup_source_sync, source_keys, uids)


def _lookup_global_sync(uids: list[str], limit: int) -> list[dict[str, Any]]:
    if not uids:
        return []
    conn = _connect()
    placeholders = ",".join("?" for _ in uids)
    rows = conn.execute(
        f"""
        SELECT source_key, uid, name, command, media_type
        FROM uid_index
        WHERE uid IN ({placeholders})
        GROUP BY source_key, uid, name, command, media_type
        ORDER BY source_key, uid
        LIMIT ?
        """,
        [*uids, max(1, int(limit))],
    ).fetchall()
    return [dict(row) for row in rows]


async def lookup_global(uids: list[str], limit: int = 2) -> list[dict[str, Any]]:
    return await asyncio.to_thread(_lookup_global_sync, uids, limit)


def _upsert_many_sync(records: list[dict[str, Any]]) -> int:
    if not records:
        return 0

    rows: list[tuple[str, str, str, str, str, str | None]] = []
    for doc in records:
        source = str(doc.get("source_key") or "").strip().lower()
        name = str(doc.get("name") or "").strip()
        if not source or not name:
            continue
        command = str(doc.get("command") or "/name").strip() or "/name"
        media_type = str(doc.get("media_type") or "unknown").strip() or "unknown"
        updated_at = doc.get("updated_at")
        updated_text = (
            updated_at.isoformat()
            if hasattr(updated_at, "isoformat")
            else (str(updated_at) if updated_at else None)
        )
        uids = list(
            dict.fromkeys(
                str(x).strip()
                for x in (doc.get("file_unique_ids") or [])
                if str(x).strip()
            )
        )
        scalar = str(doc.get("telegram_file_unique_id") or "").strip()
        if scalar and scalar not in uids:
            uids.insert(0, scalar)
        for uid in uids:
            rows.append((source, uid, name, command, media_type, updated_text))

    if not rows:
        return 0

    conn = _connect()
    conn.executemany(
        """
        INSERT INTO uid_index(source_key, uid, name, command, media_type, updated_at)
        VALUES(?, ?, ?, ?, ?, ?)
        ON CONFLICT(source_key, uid) DO UPDATE SET
            name=excluded.name,
            command=excluded.command,
            media_type=excluded.media_type,
            updated_at=excluded.updated_at
        """,
        rows,
    )
    conn.commit()
    with _HOT_LOCK:
        for source, uid, name, command, media_type, _updated_text in rows:
            record = {
                "source_key": source,
                "uid": uid,
                "name": name,
                "command": command,
                "media_type": media_type,
            }
            _HOT_SOURCE[(source, uid)] = record
            sources = _HOT_UID_SOURCES.setdefault(uid, {})
            sources[source] = record
            _HOT_GLOBAL[uid] = (
                dict(next(iter(sources.values())))
                if len(sources) == 1
                else None
            )
    return len(rows)


async def upsert_document(doc: dict[str, Any] | None) -> int:
    return await asyncio.to_thread(_upsert_many_sync, [doc] if doc else [])


async def upsert_documents(docs: Iterable[dict[str, Any]]) -> int:
    return await asyncio.to_thread(_upsert_many_sync, list(docs))


def _meta_get_sync(key: str) -> str | None:
    row = _connect().execute(
        "SELECT value FROM meta WHERE key = ?",
        (key,),
    ).fetchone()
    return str(row["value"]) if row else None


def _meta_set_sync(key: str, value: str) -> None:
    conn = _connect()
    conn.execute(
        """
        INSERT INTO meta(key, value) VALUES(?, ?)
        ON CONFLICT(key) DO UPDATE SET value=excluded.value
        """,
        (key, value),
    )
    conn.commit()


async def get_meta(key: str) -> str | None:
    return await asyncio.to_thread(_meta_get_sync, key)


async def set_meta(key: str, value: str) -> None:
    await asyncio.to_thread(_meta_set_sync, key, value)


def _stats_sync() -> dict[str, int]:
    conn = _connect()
    row = conn.execute("SELECT COUNT(*) AS count FROM uid_index").fetchone()
    with _HOT_LOCK:
        return {
            "sqlite_rows": int(row["count"]) if row else 0,
            "ram_entries": len(_HOT_SOURCE),
        }


async def get_stats() -> dict[str, int]:
    return await asyncio.to_thread(_stats_sync)
