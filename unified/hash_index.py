from __future__ import annotations

import asyncio
import logging
from collections import Counter
from threading import RLock
from typing import Any

from unified.config import settings

log = logging.getLogger(__name__)

_LOCK = RLock()
_READY = False
_RECORDS: dict[str, dict[str, Any]] = {}
_BUCKETS: dict[tuple[str, str, str], set[str]] = {}
_SOURCES: set[str] = set()
_PENDING: dict[str, dict[str, Any] | None] = {}


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
    out: list[str] = []
    consumed = 0
    for i in range(count):
        size = base + (1 if i < extra else 0)
        shift = bits - consumed - size
        out.append(format((number >> shift) & ((1 << size) - 1), "x"))
        consumed += size
    return out


def _record_chunks(record: dict[str, Any], field: str, hash_field: str) -> list[str]:
    values = record.get(field)
    if isinstance(values, (list, tuple)):
        normalized = [str(x).strip().lower() for x in values if str(x).strip()]
        if normalized:
            return list(dict.fromkeys(normalized))
    return _chunks(str(record.get(hash_field) or ""))


def _record_key(doc: dict[str, Any]) -> str:
    return str(doc.get("_id") or "").strip()


def _remove_locked(key: str) -> None:
    old = _RECORDS.pop(key, None)
    if not old:
        return

    source = str(old.get("source_key") or "").strip().lower()
    for kind, field, hash_field in (
        ("p", "phash_chunks", "phash"),
        ("d", "dhash_chunks", "dhash"),
    ):
        for chunk in _record_chunks(old, field, hash_field):
            bucket = _BUCKETS.get((source, kind, chunk))
            if bucket is None:
                continue
            bucket.discard(key)
            if not bucket:
                _BUCKETS.pop((source, kind, chunk), None)


def _insert_locked(doc: dict[str, Any]) -> None:
    key = _record_key(doc)
    source = str(doc.get("source_key") or "").strip().lower()
    media_type = str(doc.get("media_type") or "photo").strip().lower()
    if not key or not source or media_type not in {"photo", "image"}:
        return

    record = {
        "_id": doc.get("_id"),
        "name": doc.get("name"),
        "command": doc.get("command"),
        "source_key": source,
        "media_type": media_type,
        "phash": doc.get("phash"),
        "phash_large": doc.get("phash_large"),
        "dhash": doc.get("dhash"),
        "whash": doc.get("whash"),
        "colorhash": doc.get("colorhash"),
        "phash_chunks": list(doc.get("phash_chunks") or []),
        "dhash_chunks": list(doc.get("dhash_chunks") or []),
    }
    if not record["phash"] and not record["dhash"]:
        return

    _RECORDS[key] = record
    _SOURCES.add(source)

    for kind, field, hash_field in (
        ("p", "phash_chunks", "phash"),
        ("d", "dhash_chunks", "dhash"),
    ):
        for chunk in _record_chunks(record, field, hash_field):
            _BUCKETS.setdefault((source, kind, chunk), set()).add(key)


def remember_document(doc: dict[str, Any] | None) -> None:
    """Hot-sync one Mongo document into the process-local photo hash index."""
    global _READY
    if not doc:
        return
    key = _record_key(doc)
    if not key:
        return

    with _LOCK:
        if not _READY:
            _PENDING[key] = dict(doc)
            return
        _remove_locked(key)
        _insert_locked(doc)


def is_ready() -> bool:
    with _LOCK:
        return _READY


async def warm_photo_hash_index(characters) -> int:
    """Build a compact RAM candidate index from Mongo without changing Mongo."""
    global _READY

    projection = {
        "_id": 1,
        "name": 1,
        "command": 1,
        "source_key": 1,
        "media_type": 1,
        "phash": 1,
        "phash_large": 1,
        "dhash": 1,
        "whash": 1,
        "colorhash": 1,
        "phash_chunks": 1,
        "dhash_chunks": 1,
    }
    query = {
        "media_type": {"$in": ["photo", "image"]},
        "$or": [
            {"phash": {"$exists": True, "$ne": None}},
            {"dhash": {"$exists": True, "$ne": None}},
        ],
    }

    local_records: dict[str, dict[str, Any]] = {}
    local_buckets: dict[tuple[str, str, str], set[str]] = {}
    local_sources: set[str] = set()

    try:
        cursor = characters.find(query, projection).batch_size(
            max(100, min(5000, int(settings.uid_index_backfill_batch)))
        )
        async for raw in cursor:
            key = _record_key(raw)
            source = str(raw.get("source_key") or "").strip().lower()
            if not key or not source:
                continue
            media_type = str(raw.get("media_type") or "photo").strip().lower()
            if media_type not in {"photo", "image"}:
                continue

            record = {
                "_id": raw.get("_id"),
                "name": raw.get("name"),
                "command": raw.get("command"),
                "source_key": source,
                "media_type": media_type,
                "phash": raw.get("phash"),
                "phash_large": raw.get("phash_large"),
                "dhash": raw.get("dhash"),
                "whash": raw.get("whash"),
                "colorhash": raw.get("colorhash"),
                "phash_chunks": list(raw.get("phash_chunks") or []),
                "dhash_chunks": list(raw.get("dhash_chunks") or []),
            }
            if not record["phash"] and not record["dhash"]:
                continue

            local_records[key] = record
            local_sources.add(source)
            for kind, field, hash_field in (
                ("p", "phash_chunks", "phash"),
                ("d", "dhash_chunks", "dhash"),
            ):
                for chunk in _record_chunks(record, field, hash_field):
                    local_buckets.setdefault((source, kind, chunk), set()).add(key)

        with _LOCK:
            _RECORDS.clear()
            _RECORDS.update(local_records)
            _BUCKETS.clear()
            _BUCKETS.update(local_buckets)
            _SOURCES.clear()
            _SOURCES.update(local_sources)

            pending = list(_PENDING.items())
            _PENDING.clear()
            _READY = True
            for key, doc in pending:
                _remove_locked(key)
                if doc:
                    _insert_locked(doc)

        log.info(
            "HASH RAM index ready records=%s buckets=%s sources=%s",
            len(local_records),
            len(local_buckets),
            len(local_sources),
        )
        return len(local_records)
    except asyncio.CancelledError:
        raise
    except Exception:
        log.exception("HASH RAM index warm failed")
        return 0


def lookup_photo_candidates(
    scope: list[str] | None,
    phash: str | None,
    dhash: str | None,
    limit: int = 200,
) -> list[dict[str, Any]]:
    """Return likely photo candidates ranked by shared pHash/dHash chunks."""
    if not phash and not dhash:
        return []

    with _LOCK:
        if not _READY:
            return []

        sources = {
            str(source).strip().lower()
            for source in (scope or ())
            if str(source).strip()
        }
        if not sources:
            sources = set(_SOURCES)

        votes: Counter[str] = Counter()
        queries = (
            ("p", _chunks(phash)),
            ("d", _chunks(dhash)),
        )
        for source in sources:
            for kind, chunks in queries:
                for chunk in chunks:
                    for key in _BUCKETS.get((source, kind, chunk), ()):
                        votes[key] += 1

        if not votes:
            return []

        keys = sorted(votes, key=lambda key: (-votes[key], key))
        keys = keys[: max(1, int(limit))]
        return [dict(_RECORDS[key]) for key in keys if key in _RECORDS]


__all__ = [
    "is_ready",
    "lookup_photo_candidates",
    "remember_document",
    "warm_photo_hash_index",
]
