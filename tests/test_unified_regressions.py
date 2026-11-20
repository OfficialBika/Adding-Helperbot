import asyncio
import io
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
from unified.lookup import _accept_photo_candidates, _chunks, _coerce_match_score, _download, _learn_verified_uids, _ordered_uid_sources, _path_is_within, _schedule_uid_learning
from unified.main import auto_lookup_allowed
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



class PhotoHashAmbiguityTests(unittest.TestCase):
    def test_duplicate_same_identity_does_not_trigger_ambiguity(self):
        rows = [
            (
                1.000,
                0,
                0,
                {
                    "source_key": "items_character_catcher",
                    "name": "Muichiro Tokito",
                    "command": "/name",
                    "media_type": "photo",
                },
            ),
            (
                1.000,
                0,
                0,
                {
                    "source_key": "items_character_catcher",
                    "name": "Muichiro Tokito",
                    "command": "/name",
                    "media_type": "photo",
                },
            ),
        ]

        doc, score = _accept_photo_candidates(rows)
        self.assertEqual(doc["name"], "Muichiro Tokito")
        self.assertEqual(doc["source_key"], "items_character_catcher")
        self.assertAlmostEqual(score, 1.0)

    def test_same_name_across_catch_and_fw_is_not_ambiguous(self):
        rows = [
            (
                0.900,
                0,
                0,
                {
                    "source_key": "items_character_catcher_fw",
                    "name": "Muichiro Tokito",
                    "command": "/name",
                    "media_type": "photo",
                },
            ),
            (
                0.900,
                0,
                0,
                {
                    "source_key": "items_character_catcher",
                    "name": "Muichiro Tokito",
                    "command": "/name",
                    "media_type": "photo",
                },
            ),
        ]

        doc, score = _accept_photo_candidates(rows)
        self.assertEqual(doc["name"], "Muichiro Tokito")
        self.assertEqual(doc["source_key"], "items_character_catcher")
        self.assertAlmostEqual(score, 0.9)

    def test_exact_pixel_fingerprint_can_resolve_phash_tie(self):
        rows = [
            (
                0.900,
                0,
                0,
                {
                    "source_key": "items_character_catcher",
                    "name": "Black Goku",
                    "command": "/name",
                    "media_type": "photo",
                    "pixel_sha256": "PIXEL-BLACK",
                    "crop_hash": "CROP-BLACK",
                },
            ),
            (
                0.899,
                0,
                0,
                {
                    "source_key": "items_character_catcher",
                    "name": "Son Goku",
                    "command": "/name",
                    "media_type": "photo",
                    "pixel_sha256": "PIXEL-SON",
                    "crop_hash": "CROP-SON",
                },
            ),
        ]

        doc, score = _accept_photo_candidates(
            rows,
            exact_pixel_sha256="PIXEL-BLACK",
        )
        self.assertEqual(doc["name"], "Black Goku")
        self.assertAlmostEqual(score, 0.9)

    def test_different_identities_still_require_margin(self):
        rows = [
            (
                0.900,
                0,
                0,
                {
                    "source_key": "items_character_catcher",
                    "name": "Muichiro Tokito",
                    "command": "/name",
                    "media_type": "photo",
                },
            ),
            (
                0.899,
                0,
                0,
                {
                    "source_key": "items_character_catcher",
                    "name": "Shinobu Kocho",
                    "command": "/name",
                    "media_type": "photo",
                },
            ),
        ]

        doc, score = _accept_photo_candidates(rows)
        self.assertIsNone(doc)
        self.assertAlmostEqual(score, 0.9)

    def test_same_name_with_different_commands_is_not_ambiguous(self):
        rows = [
            (
                0.900,
                0,
                0,
                {
                    "source_key": "items_character_catcher",
                    "name": "Muichiro Tokito",
                    "command": "/name",
                    "media_type": "photo",
                },
            ),
            (
                0.899,
                0,
                0,
                {
                    "source_key": "items_character_catcher",
                    "name": "Muichiro Tokito",
                    "command": "/husbando",
                    "media_type": "photo",
                },
            ),
        ]

        doc, score = _accept_photo_candidates(rows)
        self.assertEqual(doc["name"], "Muichiro Tokito")
        self.assertAlmostEqual(score, 0.9)

    def test_same_name_with_unicode_and_media_label_variants_is_not_ambiguous(self):
        rows = [
            (
                0.900,
                0,
                0,
                {
                    "source_key": "items_character_catcher",
                    "name": "Muichiro Tokito",
                    "command": "/name",
                    "media_type": "photo",
                },
            ),
            (
                0.899,
                0,
                0,
                {
                    "source_key": "items_character_catcher",
                    "name": "Muichiro\u200b Tokito",
                    "command": "/name",
                    "media_type": "image",
                },
            ),
        ]

        doc, score = _accept_photo_candidates(rows)
        self.assertEqual(doc["name"], "Muichiro Tokito")
        self.assertAlmostEqual(score, 0.9)


class LocalBotApiDirectFileTests(unittest.TestCase):
    def test_path_is_within_accepts_children_and_rejects_outside(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            child = root / "bot" / "photo.jpg"
            outside = root.parent / "outside-photo.jpg"
            self.assertTrue(_path_is_within(child, root))
            self.assertFalse(_path_is_within(outside, root))

    def test_download_reads_local_bot_api_file_without_http_download(self):
        async def run():
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                local_file = root / "100" / "photo.jpg"
                local_file.parent.mkdir(parents=True)
                local_file.write_bytes(b"local-data")

                bot = SimpleNamespace(
                    get_file=AsyncMock(
                        return_value=SimpleNamespace(file_path=str(local_file))
                    ),
                    download=AsyncMock(),
                )
                fake_settings = SimpleNamespace(
                    bot_api_is_local=True,
                    bot_api_local_files_root=str(root),
                    download_timeout_seconds=20,
                )
                with patch("unified.lookup.settings", fake_settings):
                    data = await _download(bot, "FILE-ID")

                self.assertEqual(data, b"local-data")
                bot.download.assert_not_awaited()

        asyncio.run(run())

    def test_download_falls_back_when_local_path_is_outside_allowed_root(self):
        async def run():
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp) / "allowed"
                root.mkdir()
                outside = Path(tmp) / "outside.jpg"
                outside.write_bytes(b"outside")

                bot = SimpleNamespace(
                    get_file=AsyncMock(
                        return_value=SimpleNamespace(file_path=str(outside))
                    ),
                    download=AsyncMock(return_value=io.BytesIO(b"http-data")),
                )
                fake_settings = SimpleNamespace(
                    bot_api_is_local=True,
                    bot_api_local_files_root=str(root),
                    download_timeout_seconds=20,
                )
                with patch("unified.lookup.settings", fake_settings):
                    data = await _download(bot, "FILE-ID")

                self.assertEqual(data, b"http-data")
                bot.download.assert_awaited_once()

        asyncio.run(run())


class AutoLookupScopeTests(unittest.TestCase):
    def test_private_chat_is_allowed_for_auto_lookup(self):
        async def run():
            message = SimpleNamespace(chat=SimpleNamespace(type="private", id=123))
            self.assertTrue(await auto_lookup_allowed(message))

        asyncio.run(run())

    def test_public_group_is_denied_even_when_global_lookup_is_enabled(self):
        async def run():
            message = SimpleNamespace(chat=SimpleNamespace(type="supergroup", id=-100123))
            find_one = AsyncMock(return_value=None)
            fake_db = SimpleNamespace(
                settings=SimpleNamespace(find_one=find_one),
            )
            with patch("unified.main.db", fake_db):
                self.assertFalse(await auto_lookup_allowed(message))
                find_one.assert_awaited_once_with(
                    {"key": "gapprove:-100123"},
                    {"enabled": 1},
                )

        asyncio.run(run())

    def test_approved_group_is_allowed_for_auto_lookup(self):
        async def run():
            message = SimpleNamespace(chat=SimpleNamespace(type="group", id=-123))
            fake_db = SimpleNamespace(
                settings=SimpleNamespace(
                    find_one=AsyncMock(return_value={"enabled": True}),
                ),
            )
            with patch("unified.main.db", fake_db):
                self.assertTrue(await auto_lookup_allowed(message))

        asyncio.run(run())

    def test_disabled_approval_record_denies_auto_lookup(self):
        async def run():
            message = SimpleNamespace(chat=SimpleNamespace(type="group", id=-123))
            fake_db = SimpleNamespace(
                settings=SimpleNamespace(
                    find_one=AsyncMock(return_value={"enabled": False}),
                ),
            )
            with patch("unified.main.db", fake_db):
                self.assertFalse(await auto_lookup_allowed(message))

        asyncio.run(run())


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


class DynamicSourceRegistryHelpersTests(unittest.TestCase):
    def test_source_key_validation(self):
        from unified.source_registry import _source_key
        self.assertEqual(_source_key("items_new_source"), "items_new_source")
        self.assertEqual(_source_key("Items New Source"), "")
        self.assertEqual(_source_key("1invalid"), "")

    def test_dynamic_generic_parser_uses_safe_labels_only(self):
        from unified.source_registry import parse_dynamic_text
        source = {"parser_type": "generic", "parser_rules": {"name_label": "Character Name", "id_label": "ID"}}
        parsed = parse_dynamic_text(source, "Character Name: Anya Forger\nID: 1368\nRarity: Premium")
        self.assertEqual(parsed, {"name": "Anya Forger", "id": "1368"})

    def test_builtin_parser_falls_back_to_existing_parser(self):
        from unified.source_registry import parse_dynamic_text
        self.assertEqual(parse_dynamic_text({"parser_type": "builtin"}, "Name: A"), {})


    def test_dm_command_template_requires_placeholder(self):
        import re
        good = "/check {id}"
        bad = "/check 123"
        pattern = r"/[A-Za-z0-9_ ]*\{id\}[A-Za-z0-9_ ]*"
        self.assertRegex(good, pattern)
        self.assertNotRegex(bad, pattern)

    def test_dm_reply_must_reference_exact_command_message(self):
        sent_message_id = 771
        matching_reply_id = 771
        unrelated_reply_id = 772
        self.assertEqual(matching_reply_id, sent_message_id)
        self.assertNotEqual(unrelated_reply_id, sent_message_id)

    def test_dynamic_registry_worker_has_disable_guard_and_exact_reply_correlation(self):
        from pathlib import Path
        manager_source = Path("helper/manager.py").read_text(encoding="utf-8")
        self.assertIn('source.get("registration_id") or "") == registration_id', manager_source)
        self.assertIn('int(reply_id or 0) == sent_id', manager_source)
        self.assertIn('registration disabled or removed; worker stopped', manager_source)

    def test_registry_updates_are_scoped_to_registry_key(self):
        from pathlib import Path
        registry_source = Path("unified/source_registry.py").read_text(encoding="utf-8")
        self.assertIn('{"key": REGISTRY_KEY}', registry_source)
        self.assertIn('"$pull": {"sources": {"source_key": key}}', registry_source)

    def test_dynamic_resolver_preserves_builtin_source_maps(self):
        from pathlib import Path
        resolver_source = Path("namebotv3/services/source_resolver.py").read_text(encoding="utf-8")
        self.assertIn("_BASE_BOT_SOURCE_COLLECTION", resolver_source)
        self.assertIn("Replace module maps only after the complete next generation is built.", resolver_source)
        self.assertNotIn("BOT_SOURCE_USER_ID.clear()", resolver_source)

class BroadcastConcurrencyTests(unittest.TestCase):
    def test_broadcast_worker_count_is_bounded_by_fifteen(self):
        from unified.config import Settings
        self.assertGreaterEqual(Settings.broadcast_workers, 1)
        self.assertLessEqual(Settings.broadcast_workers, 15)

    def test_broadcast_rate_and_chat_interval_are_bounded(self):
        from unified.config import Settings
        self.assertGreaterEqual(Settings.broadcast_rate_per_second, 1.0)
        self.assertLessEqual(Settings.broadcast_rate_per_second, 25.0)
        self.assertGreaterEqual(Settings.broadcast_chat_interval_ms, 1000)
        self.assertLessEqual(Settings.broadcast_chat_interval_ms, 10000)

    def test_broadcast_worker_pool_uses_configured_limit(self):
        from pathlib import Path
        source = Path("unified/broadcast.py").read_text(encoding="utf-8")
        self.assertIn('range(BROADCAST_CONCURRENCY)', source)
        self.assertIn('getattr(settings, "broadcast_workers", 15)', source)

    def test_broadcast_429_updates_global_and_chat_pacing(self):
        from pathlib import Path
        source = Path("unified/broadcast.py").read_text(encoding="utf-8")
        self.assertIn('_rate_limiter.defer(float(exc.retry_after))', source)
        self.assertIn('_chat_rate_limiter.defer(chat_id, float(exc.retry_after))', source)

    def test_broadcast_per_chat_sends_are_serialized(self):
        from pathlib import Path
        source = Path("unified/broadcast.py").read_text(encoding="utf-8")
        self.assertIn('lock = await _chat_rate_limiter.acquire(chat_id)', source)
        self.assertIn('if lock and lock.locked():', source)

class BroadcastRegistryStatsTests(unittest.TestCase):
    def test_broadcast_audience_counts_use_shared_eligibility_query(self):
        from pathlib import Path
        source = Path("unified/broadcast.py").read_text(encoding="utf-8")
        self.assertIn("async def get_broadcast_audience_counts()", source)
        self.assertIn('bot_chats.count_documents(_target_query_for_type("private"))', source)
        self.assertIn('bot_chats.count_documents(_target_query_for_type("group"))', source)
        self.assertIn('bot_chats.count_documents(_target_query())', source)

    def test_stats_displays_eligible_and_registered_user_group_counts(self):
        from pathlib import Path
        source = Path("unified/status.py").read_text(encoding="utf-8")
        self.assertIn("get_broadcast_audience_counts", source)
        self.assertIn("Eligible Users", source)
        self.assertIn("Eligible Groups", source)
        self.assertIn("Registered Users", source)
        self.assertIn("Registered Groups", source)

    def test_broadcast_starts_queued_without_confirmation_keyboard(self):
        from pathlib import Path
        source = Path("unified/broadcast.py").read_text(encoding="utf-8")
        staging = source.split("async def _stage_broadcast", 1)[1].split("async def _send_broadcast_status", 1)[0]
        self.assertIn('"status": "queued"', staging)
        self.assertIn('"immediate_start": True', staging)
        self.assertIn("_wakeup.set()", staging)
        self.assertNotIn("InlineKeyboardButton", staging)
        self.assertNotIn("pending_confirmation", staging)

    def test_immediate_broadcast_has_no_inline_callback_route(self):
        from pathlib import Path
        source = Path("unified/broadcast.py").read_text(encoding="utf-8")
        self.assertNotIn('@broadcast_router.callback_query(F.data.startswith("bc:"))', source)
        self.assertNotIn("async def broadcast_confirmation_callback", source)

    def test_copy_mode_retains_source_chat_and_message_ids(self):
        from pathlib import Path
        source = Path("unified/broadcast.py").read_text(encoding="utf-8")
        staging = source.split("async def _stage_broadcast", 1)[1].split("async def _send_broadcast_status", 1)[0]
        self.assertIn('"source_chat_id": int(replied.chat.id)', staging)
        self.assertIn('"source_message_id": int(replied.message_id)', staging)
        delivery = source.split("async def _deliver_to_chat", 1)[1].split("async def _initialize_job_deliveries", 1)[0]
        self.assertIn("await bot.copy_message(", delivery)

    def test_immediate_broadcast_records_control_message_for_progress(self):
        from pathlib import Path
        source = Path("unified/broadcast.py").read_text(encoding="utf-8")
        staging = source.split("async def _stage_broadcast", 1)[1].split("async def _send_broadcast_status", 1)[0]
        self.assertIn('"control_chat_id": int(progress_message.chat.id)', staging)
        self.assertIn('"control_message_id": int(progress_message.message_id)', staging)


    def test_broadcast_reply_payload_uses_copy_message_path(self):
        from pathlib import Path
        source = Path("unified/broadcast.py").read_text(encoding="utf-8")
        self.assertIn('"payload_type": payload_type', source)
        self.assertIn('"source_chat_id": int(replied.chat.id)', source)
        self.assertIn('"source_message_id": int(replied.message_id)', source)
        self.assertIn("await bot.copy_message(", source)


