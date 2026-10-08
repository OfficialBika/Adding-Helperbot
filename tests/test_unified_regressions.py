import os
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import AsyncMock, patch

os.environ.setdefault("MONGO_URI", "mongodb://127.0.0.1:27017")
os.environ.setdefault("DB_NAME", "ci_test")

from unified.ingest import _media_info
from unified.parser import extract_character_id, extract_name
from unified.source_resolver import (
    grabber_source_variant,
    output_command_from_message,
    resolve_source_collection,
    resolve_trusted_inline_collection,
)
from unified.source_whitelist import is_allowed_source
from unified.status import RuntimeMetrics
from unified.store import _index_source_variant, save_character


class AddingOnlySourceTests(unittest.TestCase):
    def test_hallow_direct_bot_resolves(self):
        msg = SimpleNamespace(
            from_user=SimpleNamespace(id=8688011915, username="Characters_Hallow_bot", is_bot=True),
            via_bot=None, forward_origin=None, forward_from=None, forward_from_chat=None,
            sender_chat=None, text="", caption="", external_reply=None,
        )
        self.assertEqual(resolve_source_collection(msg), "items_characters_hallow")
        self.assertEqual(output_command_from_message(msg, "items_characters_hallow"), "/hallow")

    def test_catcher_logs_resolves(self):
        msg = SimpleNamespace(
            from_user=SimpleNamespace(id=123, username="helper", is_bot=False),
            forward_origin=SimpleNamespace(
                chat=SimpleNamespace(id=-1001, username="Character_Catcher_Logs", title="Character Catcher Logs"),
                message_id=42,
            ),
            forward_from_chat=None, forward_from=None, sender_chat=None, via_bot=None,
            text="", caption="Character Name: Rin Xi", external_reply=None,
        )
        self.assertEqual(resolve_source_collection(msg), "items_character_catcher_fw")

    def test_helper_inline_character_resolves(self):
        msg = SimpleNamespace(
            from_user=SimpleNamespace(id=999, username="helper", is_bot=False),
            via_bot=None, forward_origin=None, forward_from=None, sender_chat=None,
            forward_from=None, text="OwO! Check out this character",
            caption="🆔 30: Ayaka", external_reply=None,
        )
        self.assertEqual(resolve_trusted_inline_collection(msg), "items_character_catcher")

    def test_grabber_variant_is_stable(self):
        msg = SimpleNamespace(
            from_user=SimpleNamespace(id=6546492683, username="Husbando_Grabber_Bot", is_bot=True),
            via_bot=None, forward_origin=None, forward_from=None, sender_chat=None,
            text="", caption="", external_reply=None,
        )
        self.assertEqual(grabber_source_variant(msg), "husbando_grabber")


class AddingOnlyStoreTests(unittest.IsolatedAsyncioTestCase):
    async def test_media_without_unique_uid_is_rejected(self):
        result = await save_character(
            name="Test Character",
            command="/hallow",
            source_key="items_characters_hallow",
            media_type="photo",
            file_unique_id="",
        )
        self.assertEqual(result["status"], "skipped")
        self.assertEqual(result["reason"], "missing_file_unique_id")

    async def test_new_record_has_no_fingerprint_fields(self):
        existing_doc = {
            "_id": "mongo-id",
            "name": "Rin Xi",
            "source_key": "items_test",
            "character_id": "7",
            "file_unique_ids": ["UID-1"],
        }
        fake_collection = SimpleNamespace(
            find_one=AsyncMock(side_effect=[None, existing_doc]),
            insert_one=AsyncMock(),
            update_one=AsyncMock(),
        )
        with patch("unified.store.characters", fake_collection):
            result = await save_character(
                name="Rin Xi",
                command="/hallow",
                source_key="items_test",
                character_id="7",
                media_type="photo",
                file_unique_id="UID-1",
                file_id="FILE-1",
                file_unique_ids=["UID-1"],
                file_ids=["FILE-1"],
            )
        self.assertEqual(result["status"], "saved")
        inserted = fake_collection.insert_one.await_args.args[0]
        for forbidden in ("sha256", "phash", "dhash", "whash", "colorhash", "crop_hash", "video_signature"):
            self.assertNotIn(forbidden, inserted)

    async def test_hallow_uses_uid_identity_not_character_id(self):
        fake_collection = SimpleNamespace(
            find_one=AsyncMock(return_value=None),
            insert_one=AsyncMock(),
            update_one=AsyncMock(),
        )
        with patch("unified.store.characters", fake_collection):
            result = await save_character(
                name="Yoru",
                command="/hallow",
                source_key="items_characters_hallow",
                character_id="999",
                media_type="photo",
                file_unique_id="UID-9",
            )
        self.assertEqual(result["status"], "saved")
        identity = fake_collection.find_one.await_args.args[0]
        self.assertEqual(identity, {"source_key": "items_characters_hallow", "file_unique_ids": "UID-9"})


class AddingOnlyUtilityTests(unittest.TestCase):
    def test_parser_keeps_name_and_id(self):
        self.assertEqual(extract_name("Name: Rin Xi\nID: 123"), "Rin Xi")
        self.assertEqual(extract_character_id("Name: Rin Xi\nID: 123"), "123")

    def test_whitelist_accepts_known_direct_source_bot(self):
        msg = SimpleNamespace(
            from_user=SimpleNamespace(id=8688011915, username="Characters_Hallow_bot", is_bot=True),
            forward_origin=None, forward_from=None, forward_from_chat=None, via_bot=None,
        )
        self.assertTrue(is_allowed_source(msg))

    def test_media_info_collects_all_photo_unique_ids(self):
        photo1 = SimpleNamespace(file_id="F1", file_unique_id="U1", width=100, height=100, file_size=1000)
        photo2 = SimpleNamespace(file_id="F2", file_unique_id="U2", width=200, height=200, file_size=2000)
        msg = SimpleNamespace(photo=[photo1, photo2], video=None, animation=None, document=None)
        info = _media_info(msg)
        self.assertEqual(info["file_unique_id"], "U2")
        self.assertEqual(info["file_unique_ids"], ["U1", "U2"])

    def test_grabber_unknown_index_uses_uid(self):
        self.assertEqual(
            _index_source_variant("items_grabber_fw", None, file_unique_id="UID-1"),
            "unknown_uid:UID-1",
        )

    def test_metrics_are_adding_only(self):
        metrics = RuntimeMetrics()
        metrics.record_ingest("saved")
        metrics.record_ingest("updated")
        metrics.record_ingest("skipped")
        self.assertEqual(metrics.snapshot(), {
            "ingest_total": 3,
            "ingest_saved": 1,
            "ingest_updated": 1,
            "ingest_skipped": 1,
        })


class AddingOnlyArchitectureTests(unittest.TestCase):
    def test_search_runtime_modules_are_absent(self):
        for path in (
            Path("namebotv3"),
            Path("unified/lookup.py"),
            Path("unified/lookup_cache.py"),
            Path("unified/hash_index.py"),
            Path("unified/uid_index.py"),
            Path("unified/services/force_join.py"),
        ):
            self.assertFalse(path.exists(), f"forbidden path still exists: {path}")

    def test_adding_runtime_has_no_search_imports(self):
        files = (
            Path("unified/main.py"), Path("unified/ingest.py"),
            Path("unified/store.py"), Path("unified/status.py"),
            Path("unified/config.py"), Path("unified/source_resolver.py"),
            Path("unified/source_whitelist.py"),
        )
        forbidden_tokens = (
            "lookup_message", "auto_lookup", "uid_index", "hash_index",
            "force_join", "result_formatter", "services.lookup",
        )
        for path in files:
            text = path.read_text(encoding="utf-8")
            for token in forbidden_tokens:
                self.assertNotIn(token, text, f"{token} remains in {path}")


if __name__ == "__main__":
    unittest.main()
