import asyncio
import tempfile
import unittest
import sys
import os
from pathlib import Path

os.environ.setdefault("MONGO_URI", "mongodb://127.0.0.1:27017")
os.environ.setdefault("DB_NAME", "ci_test")

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "namebotv3"))
sys.path.insert(0, str(ROOT))
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import AsyncMock, patch

from unified.config import Settings
from unified.lookup import _chunks, _coerce_match_score, _exact_find, _learn_verified_uids, _ordered_uid_sources, _schedule_uid_learning
import unified.auth as auth
import unified.hash_index as hash_index
import unified.services.force_join as force_join
import unified.uid_index as uid_index


class LookupOrderingTests(unittest.TestCase):
    def test_catch_sources_are_always_deterministic(self):
        self.assertEqual(
            _ordered_uid_sources(["items_character_catcher_fw"]),
            ["items_character_catcher", "items_character_catcher_fw"],
        )
        self.assertEqual(
            _ordered_uid_sources(
                ["other", "items_character_catcher_fw", "items_character_catcher"]
            ),
            [
                "items_character_catcher",
                "items_character_catcher_fw",
                "other",
            ],
        )

    def test_non_catch_scope_keeps_requested_order(self):
        self.assertEqual(
            _ordered_uid_sources(["hallow", "grab"]),
            ["hallow", "grab"],
        )

    def test_hash_chunking_is_stable(self):
        chunks = _chunks("0123456789abcdef", count=4)
        self.assertEqual(chunks, ["123", "4567", "89ab", "cdef"])

    def test_hash_match_score_normalization_accepts_numbers(self):
        score, reason = _coerce_match_score(0.981)
        self.assertAlmostEqual(score, 0.981)
        self.assertEqual(reason, "phash_fast:0.981")

    def test_hash_match_score_normalization_accepts_reason_strings(self):
        score, reason = _coerce_match_score("phash_ram:1.000")
        self.assertAlmostEqual(score, 1.0)
        self.assertEqual(reason, "phash_ram:1.000")

    def test_hash_match_score_normalization_rejects_bad_values_without_raising(self):
        score, reason = _coerce_match_score("not-a-score")
        self.assertEqual(score, 0.0)
        self.assertEqual(reason, "not-a-score")

    def test_uid_learning_scheduler_is_defined(self):
        self.assertTrue(callable(_schedule_uid_learning))


class LookupFastPathTests(unittest.TestCase):
    def test_exact_lookup_checks_canonical_uid_before_legacy_fields(self):
        primary = {
            "_id": "doc-primary",
            "name": "Primary",
            "command": "/name",
            "source_key": "items_character_catcher",
            "media_type": "photo",
        }

        async def fake_find_one(query, projection=None):
            if "file_unique_ids" in query and query.get("source_key") == "items_character_catcher":
                return primary
            return None

        with patch("unified.lookup.characters.find_one", new=AsyncMock(side_effect=fake_find_one)) as find_one:
            result = asyncio.run(
                _exact_find(
                    ["items_character_catcher", "items_character_catcher_fw"],
                    ["UID-FAST"],
                )
            )

        self.assertEqual(result, primary)
        self.assertEqual(find_one.await_count, 2)
        for call in find_one.await_args_list:
            query = call.args[0]
            self.assertNotIn("telegram_file_unique_id", query)
            self.assertNotIn("photo_file_unique_id", query)
            self.assertNotIn("video_file_unique_id", query)


class HashIndexFastPathTests(unittest.TestCase):
    def test_photo_candidates_use_bucket_keys_when_available(self):
        target_hash = "0123456789abcdef"
        target = {
            "_id": "target",
            "name": "Target",
            "command": "/name",
            "source_key": "items_character_catcher",
            "media_type": "photo",
            "phash": target_hash,
            "phash_chunks": hash_index._chunks(target_hash),
            "dhash_chunks": [],
            "_phash_int": int(target_hash, 16),
            "_dhash_int": None,
        }
        legacy = dict(target)
        legacy["_id"] = "legacy"
        legacy["name"] = "Legacy"
        legacy["phash"] = "ffffffffffffffff"
        legacy["phash_chunks"] = []
        legacy["_phash_int"] = int(legacy["phash"], 16)

        with hash_index._LOCK:
            old_ready = hash_index._READY
            old_records = dict(hash_index._RECORDS)
            old_buckets = {key: set(value) for key, value in hash_index._BUCKETS.items()}
            old_sources = set(hash_index._SOURCES)
            old_source_keys = {key: set(value) for key, value in hash_index._SOURCE_KEYS.items()}
            hash_index._READY = True
            hash_index._RECORDS.clear()
            hash_index._BUCKETS.clear()
            hash_index._SOURCES.clear()
            hash_index._SOURCE_KEYS.clear()
            hash_index._RECORDS.update({"target": target, "legacy": legacy})
            hash_index._SOURCES.add("items_character_catcher")
            hash_index._SOURCE_KEYS["items_character_catcher"] = {"target", "legacy"}
            for chunk in target["phash_chunks"]:
                hash_index._BUCKETS.setdefault(("items_character_catcher", "p", chunk), set()).add("target")

        try:
            results = hash_index.lookup_photo_candidates(
                ["items_character_catcher"], target_hash, None, limit=10
            )
            result_ids = {doc["_id"] for doc in results}
            self.assertIn("target", result_ids)
            self.assertNotIn("legacy", result_ids)
        finally:
            with hash_index._LOCK:
                hash_index._READY = old_ready
                hash_index._RECORDS.clear()
                hash_index._RECORDS.update(old_records)
                hash_index._BUCKETS.clear()
                hash_index._BUCKETS.update(old_buckets)
                hash_index._SOURCES.clear()
                hash_index._SOURCES.update(old_sources)
                hash_index._SOURCE_KEYS.clear()
                hash_index._SOURCE_KEYS.update(old_source_keys)


class LookupGateCacheTests(unittest.TestCase):
    def test_global_lookup_gate_is_cached(self):
        auth._global_lookup_cache = None
        with patch("unified.auth.db.settings.find_one", new=AsyncMock(return_value={"key": "global_lookup", "enabled": True})) as find_one:
            self.assertTrue(asyncio.run(auth.get_global_lookup_enabled()))
            self.assertTrue(asyncio.run(auth.get_global_lookup_enabled()))
        find_one.assert_awaited_once()

    def test_force_join_gate_is_cached(self):
        force_join._enabled_cache = None
        with patch("unified.services.force_join._channels", return_value=((1, "https://t.me/a", "A"),)):
            with patch.object(force_join, "settings", SimpleNamespace(force_join_enabled=True)):
                with patch("unified.services.force_join.db.settings.find_one", new=AsyncMock(return_value={"key": "force_join:enabled", "enabled": True})) as find_one:
                    self.assertTrue(asyncio.run(force_join._enabled()))
                    self.assertTrue(asyncio.run(force_join._enabled()))
        find_one.assert_awaited_once()

class ForceJoinConfigTests(unittest.TestCase):
    def test_matching_multi_channel_configuration_is_valid(self):
        settings = Settings(
            force_join_chat_ids=(1, 2, 3),
            force_join_urls=("https://t.me/a", "https://t.me/b", "https://t.me/c"),
            force_join_titles=("A", "B", "C"),
        )
        self.assertEqual(len(settings.force_join_chat_ids), 3)
        self.assertEqual(settings.force_join_titles, ("A", "B", "C"))

    def test_mismatched_urls_are_rejected(self):
        with self.assertRaises(ValueError):
            Settings(
                force_join_chat_ids=(1, 2, 3),
                force_join_urls=("https://t.me/a", "https://t.me/b"),
                force_join_titles=("A", "B", "C"),
            )

    def test_mismatched_titles_are_rejected(self):
        with self.assertRaises(ValueError):
            Settings(
                force_join_chat_ids=(1, 2, 3),
                force_join_urls=("https://t.me/a", "https://t.me/b", "https://t.me/c"),
                force_join_titles=("A", "B"),
            )


class UIDIndexTests(unittest.TestCase):
    def test_source_priority_and_global_ambiguity(self):
        with tempfile.TemporaryDirectory() as tmp:
            fake_settings = SimpleNamespace(uid_index_path=str(Path(tmp) / "uid.sqlite3"))
            with patch.object(uid_index, "settings", fake_settings):
                with uid_index._HOT_LOCK:
                    uid_index._HOT_SOURCE.clear()
                    uid_index._HOT_UID_SOURCES.clear()
                    uid_index._HOT_GLOBAL.clear()
                asyncio.run(uid_index.ensure_uid_index())

                asyncio.run(
                    uid_index.upsert_documents(
                        [
                            {
                                "source_key": "items_character_catcher_fw",
                                "name": "FW",
                                "command": "/name",
                                "media_type": "photo",
                                "file_unique_ids": ["UID1"],
                            },
                            {
                                "source_key": "items_character_catcher",
                                "name": "Catch",
                                "command": "/name",
                                "media_type": "photo",
                                "file_unique_ids": ["UID1"],
                            },
                        ]
                    )
                )

                doc = uid_index.lookup_hot_source(
                    ["items_character_catcher", "items_character_catcher_fw"],
                    ["UID1"],
                )
                self.assertEqual(doc["source_key"], "items_character_catcher")

                # A UID present in multiple source namespaces must not be
                # treated as globally unique by the RAM accelerator.
                self.assertEqual(uid_index.lookup_hot_global(["UID1"]), [])

                sqlite_doc = asyncio.run(
                    uid_index.lookup_source(
                        ["items_character_catcher", "items_character_catcher_fw"],
                        ["UID1"],
                    )
                )
                self.assertEqual(sqlite_doc["source_key"], "items_character_catcher")

    def test_hash_verified_uid_is_learned_into_mongo_uid_array(self):
        matched = {
            "_id": "mongo-doc-1",
            "source_key": "items_character_catcher",
            "name": "Rin Xi",
        }
        update_result = SimpleNamespace(modified_count=1)
        with patch("unified.lookup.characters.update_one", new=AsyncMock(return_value=update_result)) as update:
            asyncio.run(
                _learn_verified_uids(
                    matched,
                    ["UID-A", "UID-B", "UID-A"],
                )
            )

        update.assert_awaited_once_with(
            {"_id": "mongo-doc-1", "source_key": "items_character_catcher"},
            {"$addToSet": {"file_unique_ids": {"$each": ["UID-A", "UID-B"]}}},
        )

    def test_hash_uid_learning_failure_does_not_raise(self):
        matched = {
            "_id": "mongo-doc-2",
            "source_key": "items_character_catcher_fw",
            "name": "Rin Xi",
        }
        with patch(
            "unified.lookup.characters.update_one",
            new=AsyncMock(side_effect=RuntimeError("temporary mongo failure")),
        ):
            asyncio.run(_learn_verified_uids(matched, ["UID-C"]))


    def test_verified_uid_is_immediately_hot_and_persistable(self):
        with tempfile.TemporaryDirectory() as tmp:
            fake_settings = SimpleNamespace(uid_index_path=str(Path(tmp) / "uid.sqlite3"))
            with patch.object(uid_index, "settings", fake_settings):
                with uid_index._HOT_LOCK:
                    uid_index._HOT_SOURCE.clear()
                    uid_index._HOT_UID_SOURCES.clear()
                    uid_index._HOT_GLOBAL.clear()
                asyncio.run(uid_index.ensure_uid_index())
                value = {
                    "name": "Rin Xi",
                    "command": "/name",
                    "media_type": "photo",
                }
                uid_index.remember_hot_source("items_character_catcher", ["UID-HOT"], value)
                hot = uid_index.lookup_hot_source(
                    ["items_character_catcher"], ["UID-HOT"]
                )
                self.assertEqual(hot["name"], "Rin Xi")
                self.assertEqual(hot["source_key"], "items_character_catcher")
                rows = asyncio.run(
                    uid_index.persist_uid_mappings(
                        "items_character_catcher", ["UID-HOT"], value
                    )
                )
                self.assertEqual(rows, 1)
                sqlite_doc = asyncio.run(
                    uid_index.lookup_source(
                        ["items_character_catcher"], ["UID-HOT"]
                    )
                )
                self.assertEqual(sqlite_doc["name"], "Rin Xi")


if __name__ == "__main__":
    unittest.main()
