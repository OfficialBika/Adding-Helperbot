from __future__ import annotations

import time
from collections import OrderedDict
from dataclasses import dataclass

from unified.config import settings


@dataclass(frozen=True, slots=True)
class LookupCacheItem:
    name: str
    command: str
    source_key: str
    media_type: str


class PositiveUIDCache:
    """Small in-process exact-UID cache.

    Only successful UID -> (name, command) mappings are cached.
    Misses are never cached, so newly ingested records become visible
    immediately after the first Mongo lookup.
    """

    def __init__(self, max_items: int = 300_000, ttl_seconds: int = 3600) -> None:
        self.max_items = max(1, int(max_items))
        self.ttl_seconds = max(1, int(ttl_seconds))
        self._items: OrderedDict[str, tuple[float, LookupCacheItem]] = OrderedDict()

    @staticmethod
    def _key(uid: str, source: str | None = None) -> str:
        uid = str(uid or "").strip()
        if source:
            return f"src:{str(source).strip().lower()}:{uid}"
        return f"all:{uid}"

    def get(self, uid: str, source: str | None = None) -> LookupCacheItem | None:
        key = self._key(uid, source)
        item = self._items.get(key)
        if item is None:
            return None
        expires_at, value = item
        if expires_at <= time.monotonic():
            self._items.pop(key, None)
            return None
        self._items.move_to_end(key)
        return value

    def set(self, uid: str, value: dict, source: str | None = None) -> None:
        uid = str(uid or "").strip()
        name = str(value.get("name") or "").strip()
        command = str(value.get("command") or "/name").strip() or "/name"
        source_key = str(source or value.get("source_key") or "").strip().lower()
        media_type = str(value.get("media_type") or "photo").strip().lower() or "photo"
        if not uid or not name or not source_key:
            return
        key = self._key(uid, source)
        self._items[key] = (
            time.monotonic() + self.ttl_seconds,
            LookupCacheItem(name=name, command=command, source_key=source_key, media_type=media_type),
        )
        self._items.move_to_end(key)
        while len(self._items) > self.max_items:
            self._items.popitem(last=False)

    def remember(self, uids: list[str], value: dict, source: str | None = None) -> None:
        for uid in uids:
            self.set(uid, value, source)

    def invalidate(self, uids: list[str], source: str | None = None) -> None:
        for uid in uids:
            self._items.pop(self._key(uid, source), None)

    def clear(self) -> None:
        self._items.clear()

    def size(self) -> int:
        return len(self._items)


positive_uid_cache = PositiveUIDCache(
    settings.lookup_uid_cache_max_items,
    settings.lookup_uid_cache_ttl_seconds,
)
