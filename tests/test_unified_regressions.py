import io
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
from unified.lookup import _chunks, _coerce_match_score, _download, _learn_verified_uids, _ordered_uid_sources, _path_is_within, _schedule_uid_learning
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


class LocalBotApiLookupTests(unittest.TestCase):
    def test_local_file_root_guard_accepts_children_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "files"
            child = root / "photo.jpg"
            outside = Path(tmp) / "other.jpg"
            root.mkdir()
            child.write_bytes(b"child")
            outside.write_bytes(b"outside")

            self.assertTrue(_path_is_within(child, root))
            self.assertFalse(_path_is_within(outside, root))

    def test_download_reads_absolute_local_file_without_http_body_download(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "files"
            root.mkdir()
            photo = root / "photo.jpg"
            photo.write_bytes(b"local-bytes")

            bot = SimpleNamespace(
                get_file=AsyncMock(return_value=SimpleNamespace(file_path=str(photo))),
                download=AsyncMock(),
            )
            fake_settings = SimpleNamespace(
                bot_api_is_local=True,
                bot_api_local_files_root=str(root),
                download_timeout_seconds=20,
            )
            import unified.lookup as lookup_module
            with patch.object(lookup_module, "settings", fake_settings):
                data = asyncio.run(_download(bot, "FILE-ID", priority="fast"))

            self.assertEqual(data, b"local-bytes")
            bot.get_file.assert_awaited_once_with("FILE-ID")
            bot.download.assert_not_awaited()

    def test_local_file_read_falls_back_when_path_is_outside_allowed_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "allowed"
            outside = Path(tmp) / "outside.jpg"
            root.mkdir()
            outside.write_bytes(b"outside")

            bot = SimpleNamespace(
                get_file=AsyncMock(return_value=SimpleNamespace(file_path=str(outside))),
                download=AsyncMock(return_value=io.BytesIO(b"http-fallback")),
            )
            fake_settings = SimpleNamespace(
                bot_api_is_local=True,
                bot_api_local_files_root=str(root),
                download_timeout_seconds=20,
            )
            import unified.lookup as lookup_module
            with patch.object(lookup_module, "settings", fake_settings):
                data = asyncio.run(_download(bot, "FILE-ID", priority="fast"))

            self.assertEqual(data, b"http-fallback")
            bot.get_file.assert_awaited_once_with("FILE-ID")
            bot.download.assert_awaited_once()


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
