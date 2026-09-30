from __future__ import annotations

import asyncio
import sqlite3
import threading
from collections import OrderedDict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

from unified.config import settings
from unified.store import characters

_LOOKUP_PROJECTION = {
    "_id": 1,
    "name": 1,
    "command": 1,
    "source_key": 1,
    "file_unique_ids": 1,
    "telegram_file_unique_id": 1,
    "file_unique_id": 1,
    "photo_file_unique_id": 1,
    "video_file_unique_id": 1,
    "media": 1,
    "updated_at": 1,
}

_SCHEMA_VERSION = 2


def _text(value: Any) -> str:
    return str(value or "").strip()


def _updated_ts(value: Any) -> float:
    if isinstance(value, datetime):
        if value.tzinfo is None:
            value = value.replace(tzinfo=timezone.utc)
        return value.timestamp()
    raw = _text(value)
    if not raw:
        return 0.0
    try:
        return datetime.fromisoformat(raw.replace("Z", "+00:00")).timestamp()
    except Exception:
        try:
            return float(raw)
        except Exception:
            return 0.0


def _doc_id(doc: dict) -> str:
    return _text(doc.get("_id"))


def _doc_uids(doc: dict) -> list[str]:
    out: list[str] = []

    def add(value: Any):
        value = _text(value)
        if value and value not in out:
            out.append(value)

    for value in doc.get("file_unique_ids") or []:
        add(value)

    for key in (
        "telegram_file_unique_id",
        "file_unique_id",
        "photo_file_unique_id",
        "video_file_unique_id",
    ):
        add(doc.get(key))

    media = doc.get("media")
    if isinstance(media, dict):
        add(media.get("file_unique_id"))

    return out


class LookupRAMCache:
    """Small positive-only source-aware hot cache.

    We deliberately cache lookup summaries, not full Mongo documents. Each
    entry is only (name, command, source), keyed by Telegram UID + source.
    """

    def __init__(self, max_items: int = 30000):
        self.max_items = max(1000, int(max_items))
        self._data: OrderedDict[tuple[str, str], tuple[str, str, str]] = OrderedDict()
        self._lock = threading.RLock()

    def get(self, uid: str, source: str) -> dict | None:
        key = (_text(uid), _text(source).lower())
        if not key[0] or not key[1]:
            return None
        with self._lock:
            item = self._data.get(key)
            if item is None:
                return None
            self._data.move_to_end(key)
            name, command, source_key = item
        return {
            "name": name,
            "command": command,
            "source_key": source_key,
        }

    def put(self, doc: dict):
        name = _text(doc.get("name"))
        source = _text(doc.get("source_key")).lower()
        if not name or not source:
            return
        command = _text(doc.get("command")) or "/name"
        for uid in _doc_uids(doc):
            key = (uid, source)
            with self._lock:
                self._data[key] = (name, command, source)
                self._data.move_to_end(key)
                while len(self._data) > self.max_items:
                    self._data.popitem(last=False)

    def clear(self):
        with self._lock:
            self._data.clear()

    def size(self) -> int:
        with self._lock:
            return len(self._data)


class LookupSQLiteIndex:
    """Local exact-UID index backed by stdlib SQLite.

    MongoDB remains the source of truth. SQLite stores only compact lookup
    summaries and Telegram UID identities; it can be rebuilt at any time.
    """

    def __init__(
        self,
        path: str = "data/lookup_index.sqlite3",
        ram_cache_max_items: int = 30000,
    ):
        self.path = Path(path)
        self.ram = LookupRAMCache(ram_cache_max_items)
        self._conn: sqlite3.Connection | None = None
        self._lock = threading.RLock()
        self._ready = False

    def _connect_sync(self):
        if self._conn is not None:
            return
        self.path.parent.mkdir(parents=True, exist_ok=True)
        conn = sqlite3.connect(
            str(self.path),
            timeout=5.0,
            check_same_thread=False,
        )
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA synchronous=NORMAL")
        conn.execute("PRAGMA temp_store=MEMORY")
        conn.execute("PRAGMA cache_size=-32768")
        conn.execute("PRAGMA busy_timeout=5000")
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS uid_index (
                uid TEXT NOT NULL,
                source_key TEXT NOT NULL,
                doc_id TEXT NOT NULL,
                name TEXT NOT NULL,
                command TEXT NOT NULL,
                updated_ts REAL NOT NULL DEFAULT 0,
                PRIMARY KEY (uid, source_key, doc_id)
            )
            """
        )
        conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_uid_source ON uid_index(uid, source_key)"
        )
        conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_uid ON uid_index(uid)"
        )
        conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_source_updated ON uid_index(source_key, updated_ts DESC)"
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS meta (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            )
            """
        )
        conn.commit()
        self._conn = conn

    def _meta_get_sync(self, key: str) -> str:
        self._connect_sync()
        row = self._conn.execute(
            "SELECT value FROM meta WHERE key = ?",
            (key,),
        ).fetchone()
        return _text(row[0]) if row else ""

    def _meta_set_sync(self, key: str, value: str):
        self._connect_sync()
        self._conn.execute(
            """
            INSERT INTO meta(key, value) VALUES(?, ?)
            ON CONFLICT(key) DO UPDATE SET value=excluded.value
            """,
            (key, _text(value)),
        )

    def _record_rows(self, doc: dict) -> list[tuple[str, str, str, str, str, float]]:
        source = _text(doc.get("source_key")).lower()
        name = _text(doc.get("name"))
        command = _text(doc.get("command")) or "/name"
        doc_id = _doc_id(doc)
        if not source or not name or not doc_id:
            return []

        updated_ts = _updated_ts(doc.get("updated_at"))
        return [
            (uid, source, doc_id, name, command, updated_ts)
            for uid in _doc_uids(doc)
        ]

    def _upsert_docs_sync(self, docs: Iterable[dict], *, populate_ram: bool = False):
        self._connect_sync()
        docs = list(docs)
        rows: list[tuple[str, str, str, str, str, float]] = []
        max_ts = 0.0

        for doc in docs:
            rows.extend(self._record_rows(doc))
            max_ts = max(max_ts, _updated_ts(doc.get("updated_at")))
            if populate_ram:
                self.ram.put(doc)

        if rows:
            self._conn.executemany(
                """
                INSERT INTO uid_index(
                    uid, source_key, doc_id, name, command, updated_ts
                ) VALUES (?, ?, ?, ?, ?, ?)
                ON CONFLICT(uid, source_key, doc_id) DO UPDATE SET
                    name=excluded.name,
                    command=excluded.command,
                    updated_ts=excluded.updated_ts
                """,
                rows,
            )

        if max_ts:
            current = _updated_ts(self._meta_get_sync("last_updated_ts"))
            if max_ts > current:
                self._meta_set_sync("last_updated_ts", str(max_ts))

        self._meta_set_sync("schema_version", str(_SCHEMA_VERSION))
        self._conn.commit()

    def _clear_sync(self):
        self._connect_sync()
        self._conn.execute("DELETE FROM uid_index")
        self._meta_set_sync("last_updated_ts", "0")
        self._meta_set_sync("schema_version", str(_SCHEMA_VERSION))
        self._meta_set_sync("build_complete", "0")
        self._conn.commit()
        self.ram.clear()

    def _lookup_source_sync(self, uids: list[str], sources: list[str]) -> dict | None:
        self._connect_sync()
        uids = list(dict.fromkeys(_text(x) for x in uids if _text(x)))
        sources = list(dict.fromkeys(_text(x).lower() for x in sources if _text(x)))
        if not uids or not sources:
            return None

        uid_marks = ",".join("?" for _ in uids)
        source_marks = ",".join("?" for _ in sources)
        rows = self._conn.execute(
            f"""
            SELECT uid, source_key, name, command, updated_ts
            FROM uid_index
            WHERE uid IN ({uid_marks})
              AND source_key IN ({source_marks})
            ORDER BY updated_ts DESC
            LIMIT 50
            """,
            [*uids, *sources],
        ).fetchall()
        if not rows:
            return None

        priority = {source: i for i, source in enumerate(sources)}
        rows.sort(key=lambda row: (priority.get(row[1], 999), -float(row[4] or 0)))
        uid, source_key, name, command, _updated_ts_value = rows[0]
        return {
            "name": name,
            "command": command or "/name",
            "source_key": source_key,
            "_lookup_uid": uid,
        }

    def _lookup_global_sync(self, uids: list[str], limit: int = 3) -> list[dict]:
        self._connect_sync()
        uids = list(dict.fromkeys(_text(x) for x in uids if _text(x)))
        if not uids:
            return []

        uid_marks = ",".join("?" for _ in uids)
        rows = self._conn.execute(
            f"""
            SELECT
                MIN(uid) AS uid,
                source_key,
                name,
                command,
                doc_id,
                MAX(updated_ts) AS updated_ts
            FROM uid_index
            WHERE uid IN ({uid_marks})
            GROUP BY source_key, doc_id, name, command
            ORDER BY updated_ts DESC
            LIMIT ?
            """,
            [*uids, max(1, int(limit))],
        ).fetchall()
        return [
            {
                "name": row[2],
                "command": row[3] or "/name",
                "source_key": row[1],
                "_lookup_uid": row[0],
                "_lookup_doc_id": row[4],
            }
            for row in rows
        ]

    def _count_sync(self) -> int:
        self._connect_sync()
        row = self._conn.execute("SELECT COUNT(*) FROM uid_index").fetchone()
        return int(row[0] if row else 0)

    def _stats_sync(self) -> dict:
        self._connect_sync()
        return {
            "rows": self._count_sync(),
            "ram_items": self.ram.size(),
            "ready": self._ready,
            "path": str(self.path),
            "last_updated_ts": self._meta_get_sync("last_updated_ts"),
        }

    async def lookup_source(self, uids: list[str], sources: list[str]) -> dict | None:
        return await asyncio.to_thread(self._locked_lookup_source, uids, sources)

    def _locked_lookup_source(self, uids: list[str], sources: list[str]) -> dict | None:
        with self._lock:
            return self._lookup_source_sync(uids, sources)

    async def lookup_global(self, uids: list[str], limit: int = 3) -> list[dict]:
        return await asyncio.to_thread(self._locked_lookup_global, uids, limit)

    def _locked_lookup_global(self, uids: list[str], limit: int = 3) -> list[dict]:
        with self._lock:
            return self._lookup_global_sync(uids, limit)

    async def upsert_document(self, doc: dict):
        if not isinstance(doc, dict):
            return
        await asyncio.to_thread(self._locked_upsert, [doc], True)

    def _locked_upsert(self, docs: list[dict], populate_ram: bool = False):
        with self._lock:
            self._upsert_docs_sync(docs, populate_ram=populate_ram)

    async def _bulk_upsert(self, docs: list[dict], *, populate_ram: bool = False):
        if not docs:
            return
        await asyncio.to_thread(self._locked_upsert, docs, populate_ram)

    async def rebuild_from_mongo(self):
        self._ready = False
        await asyncio.to_thread(self._locked_clear)

        batch: list[dict] = []
        max_ts = 0.0
        async for doc in characters.find({}, _LOOKUP_PROJECTION).batch_size(2000):
            batch.append(doc)
            max_ts = max(max_ts, _updated_ts(doc.get("updated_at")))
            if len(batch) >= 1000:
                await self._bulk_upsert(batch, populate_ram=False)
                batch = []

        if batch:
            await self._bulk_upsert(batch, populate_ram=False)

        await asyncio.to_thread(self._finish_rebuild, max_ts)
        self._ready = True

    def _finish_rebuild(self, max_ts: float):
        with self._lock:
            if max_ts:
                self._meta_set_sync("last_updated_ts", str(max_ts))
            self._meta_set_sync("build_complete", "1")
            self._conn.commit()

    async def sync_from_mongo(self):
        await asyncio.to_thread(self._connect_if_needed)
        schema, build_complete = await asyncio.to_thread(self._read_meta_pair)

        if schema != str(_SCHEMA_VERSION) or build_complete != "1":
            await self.rebuild_from_mongo()
            return

        indexed_rows = await asyncio.to_thread(self._locked_count)
        if indexed_rows == 0:
            await self.rebuild_from_mongo()
            return

        last_ts = await asyncio.to_thread(self._read_last_updated_ts)
        from_dt = datetime.fromtimestamp(
            max(0.0, last_ts - 60.0),
            tz=timezone.utc,
        )

        batch: list[dict] = []
        async for doc in characters.find(
            {"updated_at": {"$gt": from_dt}},
            _LOOKUP_PROJECTION,
        ).sort("updated_at", 1).batch_size(2000):
            batch.append(doc)
            if len(batch) >= 1000:
                await self._bulk_upsert(batch, populate_ram=True)
                batch = []

        if batch:
            await self._bulk_upsert(batch, populate_ram=True)

        self._ready = True

    def _read_last_updated_ts(self) -> float:
        with self._lock:
            return _updated_ts(self._meta_get_sync("last_updated_ts"))

    async def ensure_ready(self):
        await asyncio.to_thread(self._connect_if_needed)
        await self.sync_from_mongo()
        self._ready = True

    async def stats(self) -> dict:
        await asyncio.to_thread(self._connect_if_needed)
        return await asyncio.to_thread(self._locked_stats)

    def _locked_count(self) -> int:
        with self._lock:
            return self._count_sync()

    def _locked_stats(self) -> dict:
        with self._lock:
            return self._stats_sync()

    async def close(self):
        await asyncio.to_thread(self._locked_close)

    def _locked_close(self):
        with self._lock:
            self._close_sync()

    def _close_sync(self):
        if self._conn is not None:
            try:
                self._conn.close()
            finally:
                self._conn = None
        self._ready = False


lookup_index = LookupSQLiteIndex(
    path=settings.lookup_sqlite_path,
    ram_cache_max_items=settings.lookup_ram_cache_max_items,
)
