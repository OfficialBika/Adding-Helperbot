from __future__ import annotations

import asyncio
import logging
import sqlite3
from collections.abc import Iterable
from pathlib import Path
from threading import local
from typing import Any

from unified.config import settings

log = logging.getLogger(__name__)

_SCHEMA_VERSION = 2
_LOCAL = local()


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


async def ensure_uid_index() -> None:
    await asyncio.to_thread(_init_sync)


def _lookup_source_sync(source_keys: list[str], uids: list[str]) -> dict[str, Any] | None:
    if not source_keys or not uids:
        return None
    conn = _connect()
    placeholders_s = ",".join("?" for _ in source_keys)
    placeholders_u = ",".join("?" for _ in uids)
    row = conn.execute(
        f"""
        SELECT source_key, uid, name, command, media_type
        FROM uid_index
        WHERE source_key IN ({placeholders_s})
          AND uid IN ({placeholders_u})
        ORDER BY rowid DESC
        LIMIT 1
        """,
        [*source_keys, *uids],
    ).fetchone()
    return dict(row) if row else None


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
