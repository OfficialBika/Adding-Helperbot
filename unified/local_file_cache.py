from __future__ import annotations

import asyncio
import logging
import sqlite3
import time
from collections import OrderedDict
from dataclasses import dataclass
from pathlib import Path
from threading import RLock, local

log = logging.getLogger(__name__)

_MEMORY_LIMIT = 8192
_PERSISTED_TTL_SECONDS = 90 * 24 * 60 * 60


@dataclass(frozen=True)
class _PathRecord:
    root: str
    path: str
    size: int
    mtime_ns: int
    file_id: str
    file_unique_id: str


class LocalFilePathCache:
    """Persistent, root-scoped cache for Local Bot API file paths.

    Telegram IDs are opaque. This cache never guesses a path from an ID: it only
    reuses a path previously returned by getFile and read successfully. Every
    cached path is revalidated against the configured root and its file stat
    before use.
    """

    def __init__(self, db_path: str | Path, *, memory_limit: int = _MEMORY_LIMIT):
        path = Path(str(db_path or "data/local_file_path_cache.sqlite3")).expanduser()
        if not path.is_absolute():
            path = Path(__file__).resolve().parents[1] / path
        self._db_path = path.resolve()
        self._memory_limit = max(128, int(memory_limit))
        self._local = local()
        self._lock = RLock()
        self._memory: OrderedDict[tuple[str, str, str], tuple[str, int, int]] = OrderedDict()
        self._persisted: set[tuple[str, str, str]] = set()

    @staticmethod
    def _root_key(root: str | Path) -> str:
        return str(Path(root).expanduser().resolve())

    @staticmethod
    def _keys(file_id: str | None, file_unique_id: str | None):
        file_key = str(file_id or "").strip()
        unique_key = str(file_unique_id or "").strip()
        if file_key:
            yield ("file_id", file_key)
        if unique_key:
            yield ("file_unique_id", unique_key)

    @staticmethod
    def _validated_snapshot(
        root: str,
        path: str | Path,
        *,
        size: int | None = None,
        mtime_ns: int | None = None,
        file_id: str = "",
        file_unique_id: str = "",
    ) -> _PathRecord | None:
        try:
            root_path = Path(root).expanduser().resolve()
            candidate = Path(path).expanduser()
            if not candidate.is_absolute():
                return None
            resolved = candidate.resolve(strict=True)
            stat = resolved.stat()
            if not resolved.is_file():
                return None
            if resolved != root_path and root_path not in resolved.parents:
                return None
            if size is not None and stat.st_size != int(size):
                return None
            if mtime_ns is not None and stat.st_mtime_ns != int(mtime_ns):
                return None
            return _PathRecord(
                root=str(root_path),
                path=str(resolved),
                size=stat.st_size,
                mtime_ns=stat.st_mtime_ns,
                file_id=str(file_id or "").strip(),
                file_unique_id=str(file_unique_id or "").strip(),
            )
        except (OSError, RuntimeError, TypeError, ValueError):
            return None

    def _connect(self) -> sqlite3.Connection:
        conn = getattr(self._local, "conn", None)
        if conn is not None and getattr(self._local, "db_path", None) == str(self._db_path):
            try:
                conn.execute("SELECT 1")
                return conn
            except sqlite3.Error:
                self._local.conn = None

        self._db_path.parent.mkdir(parents=True, exist_ok=True)
        conn = sqlite3.connect(str(self._db_path), timeout=5.0)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA busy_timeout=5000")
        try:
            conn.execute("PRAGMA journal_mode=WAL")
        except sqlite3.Error:
            # The lookup remains an optional accelerator if SQLite is busy.
            pass
        conn.execute("PRAGMA synchronous=NORMAL")
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS local_file_path_cache (
                root TEXT NOT NULL,
                key_type TEXT NOT NULL,
                file_key TEXT NOT NULL,
                path TEXT NOT NULL,
                size INTEGER NOT NULL,
                mtime_ns INTEGER NOT NULL,
                updated_at REAL NOT NULL,
                PRIMARY KEY (root, key_type, file_key)
            )
            """
        )
        conn.execute(
            "CREATE INDEX IF NOT EXISTS idx_local_file_path_updated "
            "ON local_file_path_cache(updated_at)"
        )
        conn.commit()
        self._local.conn = conn
        self._local.db_path = str(self._db_path)
        return conn

    def _memory_put(
        self,
        key: tuple[str, str, str],
        value: tuple[str, int, int],
        *,
        persisted: bool = False,
    ) -> None:
        with self._lock:
            previous = self._memory.get(key)
            if previous != value:
                self._persisted.discard(key)
            self._memory[key] = value
            self._memory.move_to_end(key)
            if persisted:
                self._persisted.add(key)
            while len(self._memory) > self._memory_limit:
                evicted, _ = self._memory.popitem(last=False)
                self._persisted.discard(evicted)

    def _memory_get(self, root: str, key_type: str, file_key: str) -> Path | None:
        key = (root, key_type, file_key)
        with self._lock:
            value = self._memory.get(key)
            if value is None:
                return None
            self._memory.move_to_end(key)

        path, size, mtime_ns = value
        snapshot = self._validated_snapshot(
            root, path, size=size, mtime_ns=mtime_ns
        )
        if snapshot is not None:
            return Path(snapshot.path)

        with self._lock:
            if self._memory.get(key) == value:
                self._memory.pop(key, None)
            self._persisted.discard(key)
        return None

    async def lookup_path(
        self,
        root: str | Path,
        file_id: str | None,
        file_unique_id: str | None = None,
    ) -> Path | None:
        """Resolve only previously learned mappings; return None on any cache error."""
        keys = list(self._keys(file_id, file_unique_id))
        if not keys:
            return None
        try:
            root_key = self._root_key(root)
            return await asyncio.to_thread(self._lookup_sync, root_key, keys)
        except Exception:
            log.debug("Local file path cache lookup failed", exc_info=True)
            return None

    def _lookup_sync(
        self,
        root: str,
        keys: list[tuple[str, str]],
    ) -> Path | None:
        for key_type, file_key in keys:
            hit = self._memory_get(root, key_type, file_key)
            if hit is not None:
                return hit

        conn = self._connect()
        stale_found = False
        for key_type, file_key in keys:
            row = conn.execute(
                """
                SELECT path, size, mtime_ns
                FROM local_file_path_cache
                WHERE root=? AND key_type=? AND file_key=?
                """,
                (root, key_type, file_key),
            ).fetchone()
            if row is None:
                continue

            snapshot = self._validated_snapshot(
                root,
                row["path"],
                size=row["size"],
                mtime_ns=row["mtime_ns"],
            )
            if snapshot is None:
                conn.execute(
                    "DELETE FROM local_file_path_cache "
                    "WHERE root=? AND key_type=? AND file_key=?",
                    (root, key_type, file_key),
                )
                stale_found = True
                continue

            self._memory_put(
                (root, key_type, file_key),
                (snapshot.path, snapshot.size, snapshot.mtime_ns),
                persisted=True,
            )
            if stale_found:
                conn.commit()
            return Path(snapshot.path)

        if stale_found:
            conn.commit()
        return None

    def remember(
        self,
        root: str | Path,
        file_id: str | None,
        file_unique_id: str | None,
        path: str | Path,
    ) -> _PathRecord | None:
        """Remember a validated file immediately in RAM; return record if it needs persistence."""
        keys = list(self._keys(file_id, file_unique_id))
        if not keys:
            return None
        try:
            root_key = self._root_key(root)
        except (OSError, RuntimeError, TypeError, ValueError):
            return None
        snapshot = self._validated_snapshot(
            root_key,
            path,
            file_id=str(file_id or "").strip(),
            file_unique_id=str(file_unique_id or "").strip(),
        )
        if snapshot is None:
            return None

        value = (snapshot.path, snapshot.size, snapshot.mtime_ns)
        needs_persist = False
        for key_type, file_key in keys:
            key = (root_key, key_type, file_key)
            with self._lock:
                old = self._memory.get(key)
                if old != value:
                    self._persisted.discard(key)
                self._memory[key] = value
                self._memory.move_to_end(key)
                if key not in self._persisted:
                    needs_persist = True
                while len(self._memory) > self._memory_limit:
                    evicted, _ = self._memory.popitem(last=False)
                    self._persisted.discard(evicted)
        return snapshot if needs_persist else None

    async def persist(self, record: _PathRecord) -> None:
        """Persist learned paths off the event loop; this cache is never authoritative."""
        try:
            await asyncio.to_thread(self._store_sync, record)
        except Exception:
            log.warning("Local file path cache persistence failed", exc_info=True)
            return
        value = (record.path, record.size, record.mtime_ns)
        with self._lock:
            for key_type, file_key in self._keys(record.file_id, record.file_unique_id):
                key = (record.root, key_type, file_key)
                if self._memory.get(key) == value:
                    self._persisted.add(key)

    def _store_sync(self, record: _PathRecord) -> None:
        # Revalidate immediately before persistence in case the path changed.
        snapshot = self._validated_snapshot(
            record.root,
            record.path,
            size=record.size,
            mtime_ns=record.mtime_ns,
            file_id=record.file_id,
            file_unique_id=record.file_unique_id,
        )
        if snapshot is None:
            return
        conn = self._connect()
        now = time.time()
        for key_type, file_key in self._keys(snapshot.file_id, snapshot.file_unique_id):
            conn.execute(
                """
                INSERT INTO local_file_path_cache
                    (root, key_type, file_key, path, size, mtime_ns, updated_at)
                VALUES (?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(root, key_type, file_key) DO UPDATE SET
                    path=excluded.path,
                    size=excluded.size,
                    mtime_ns=excluded.mtime_ns,
                    updated_at=excluded.updated_at
                """,
                (
                    snapshot.root,
                    key_type,
                    file_key,
                    snapshot.path,
                    snapshot.size,
                    snapshot.mtime_ns,
                    now,
                ),
            )
        conn.execute(
            "DELETE FROM local_file_path_cache WHERE updated_at < ?",
            (now - _PERSISTED_TTL_SECONDS,),
        )
        conn.commit()

    def _delete_sync(
        self, root: str, keys: list[tuple[str, str]], path: str
    ) -> None:
        conn = self._connect()
        for key_type, file_key in keys:
            conn.execute(
                """
                DELETE FROM local_file_path_cache
                WHERE root=? AND key_type=? AND file_key=? AND path=?
                """,
                (root, key_type, file_key, path),
            )
        conn.commit()

    async def invalidate(
        self,
        root: str | Path,
        file_id: str | None,
        file_unique_id: str | None,
        path: str | Path,
    ) -> None:
        """Forget a path that became unreadable after lookup."""
        keys = list(self._keys(file_id, file_unique_id))
        try:
            root_key = self._root_key(root)
        except (OSError, RuntimeError, TypeError, ValueError):
            return
        path_text = str(path)
        with self._lock:
            for key_type, file_key in keys:
                key = (root_key, key_type, file_key)
                value = self._memory.get(key)
                if value and value[0] == path_text:
                    self._memory.pop(key, None)
                self._persisted.discard(key)
        try:
            await asyncio.to_thread(self._delete_sync, root_key, keys, path_text)
        except Exception:
            log.debug("Local file path cache invalidation failed", exc_info=True)
