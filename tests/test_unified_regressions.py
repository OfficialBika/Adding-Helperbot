import asyncio
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from unified.config import Settings
from unified.lookup import _chunks, _ordered_uid_sources
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
        self.assertEqual(chunks, ["0123", "4567", "89ab", "cdef"])


class ForceJoinConfigTests(unittest.TestCase):
    def test_matching_multi_channel_configuration_is_valid(self):
        settings = Settings(
            force_join_chat_ids=(1, 2, 3),
            force_join_urls=("https://t.me/a", "https://t.me/b", "https://t.me/c"),
            force_join_titles=("A", "B", "C"),
        )
        self.assertEqual(len(settings.force_join_chat_ids), 3)

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


if __name__ == "__main__":
    unittest.main()
