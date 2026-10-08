import os
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import AsyncMock, patch

os.environ.setdefault("MONGO_URI", "mongodb://127.0.0.1:27017")
os.environ.setdefault("DB_NAME", "ci_test")

from helper.registry import _CACHE, parse_addnewbot, parser_names_for_source
from unified.ingest import _is_metadata_edit, _media_info
from unified.parser import extract_character_id, extract_name, parse_candidates, parse_message, parser_names
from unified.source_resolver import (
    grabber_source_variant,
    output_command_from_message,
    resolve_source_collection,
    resolve_trusted_inline_collection,
)
from unified.source_whitelist import is_allowed_source
from unified.status import RuntimeMetrics
from unified.store import _index_source_variant, save_character, update_character_metadata


class DynamicHelperBotTests(unittest.TestCase):
    def test_addnewbot_payload_is_parsed(self):
        config = parse_addnewbot(
            "/addnewbot @newcardbot\n"
            "cmd - /grab\n"
            "inlinesource - @newcardbot\n"
            "Forwardsource - @newcardchannel\n"
            "commands - /startnewcardbot,/resumenewcardbot,/startfwnewcatchbot,/resumefwnewcatchbot\n"
            "Parser1 - grab\n"
            "Parser2 - generic"
        )
        self.assertEqual(config.key, "items_newcardbot")
        self.assertEqual(config.command, "/grab")
        self.assertEqual(config.commands, (
            "/startnewcardbot",
            "/resumenewcardbot",
            "/startfwnewcatchbot",
            "/resumefwnewcatchbot",
        ))
        self.assertEqual(config.parsers, ("grab", "generic"))

    def test_dynamic_sources_and_parser_preferences(self):
        config = parse_addnewbot(
            "/addnewbot @newcardbot\n"
            "cmd - /grab\n"
            "inlinesource - @newcardbot\n"
            "Forwardsource - @newcardchannel\n"
            "commands - /startnewcardbot,/resumenewcardbot,/startfwnewcatchbot,/resumefwnewcatchbot\n"
            "Parser1 - grab\n"
            "Parser2 - generic"
        )
        previous = dict(_CACHE)
        try:
            _CACHE.clear()
            _CACHE[config.key] = config
            self.assertEqual(parser_names_for_source(config.key), ("grab_family", "generic_structured"))
            self.assertEqual(
                resolve_source_collection(
                    SimpleNamespace(
                        from_user=SimpleNamespace(id=999, username="newcardbot", is_bot=True),
                        via_bot=None, forward_origin=None, forward_from=None,
                        forward_from_chat=None, sender_chat=None, text="", caption="",
                        external_reply=None,
                    )
                ),
                "items_newcardbot",
            )
            self.assertEqual(
                output_command_from_message(
                    SimpleNamespace(
                        from_user=SimpleNamespace(id=999, username="newcardbot", is_bot=True),
                        via_bot=None, forward_origin=None, forward_from=None,
                        forward_from_chat=None, sender_chat=None, text="", caption="",
                        external_reply=None,
                    ),
                    "items_newcardbot",
                ),
                "/grab",
            )
        finally:
            _CACHE.clear()
            _CACHE.update(previous)


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
            text="OwO! Check out this character",
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

    async def test_metadata_edit_updates_existing_record_only(self):
        existing = {
            "_id": "mongo-id",
            "name": "Retsu Unahana",
            "name_key": "retsu unahana",
            "anime": "Dragon Ball",
            "rarity": "RARE",
            "character_id": "5726",
            "source_key": "items_newcardbot",
        }
        updated = dict(existing, name="Retsu Unahana New", name_key="retsu unahana new")
        fake_collection = SimpleNamespace(
            find_one=AsyncMock(side_effect=[existing, updated]),
            update_one=AsyncMock(),
        )
        with patch("unified.store.characters", fake_collection):
            result = await update_character_metadata(
                source_key="items_newcardbot",
                character_id="5726",
                name="Retsu Unahana New",
                anime="Bleach",
                rarity="NOVICE",
            )
        self.assertEqual(result["status"], "updated")
        self.assertIn("name:", result["changes"][0])
        self.assertEqual(fake_collection.update_one.await_count, 1)
        update = fake_collection.update_one.await_args.args[1]
        self.assertEqual(update["$set"]["name"], "Retsu Unahana New")
        self.assertEqual(update["$set"]["anime"], "Bleach")
        self.assertEqual(update["$set"]["rarity"], "NOVICE")

    async def test_metadata_edit_returns_already_added_when_unchanged(self):
        existing = {
            "_id": "mongo-id",
            "name": "Retsu Unahana",
            "name_key": "retsu unahana",
            "anime": "Bleach",
            "rarity": "NOVICE",
            "character_id": "5726",
            "source_key": "items_newcardbot",
        }
        fake_collection = SimpleNamespace(find_one=AsyncMock(return_value=existing))
        with patch("unified.store.characters", fake_collection):
            result = await update_character_metadata(
                source_key="items_newcardbot",
                character_id="5726",
                name="Retsu Unahana",
                anime="Bleach",
                rarity="NOVICE",
            )
        self.assertEqual(result["status"], "already_added")
        self.assertEqual(result["changes"], [])

    async def test_metadata_edit_never_creates_missing_record(self):
        fake_collection = SimpleNamespace(find_one=AsyncMock(return_value=None), insert_one=AsyncMock())
        with patch("unified.store.characters", fake_collection):
            result = await update_character_metadata(
                source_key="items_newcardbot",
                character_id="5726",
                name="Retsu Unahana",
                anime="Bleach",
                rarity="NOVICE",
            )
        self.assertEqual(result["status"], "skipped")
        self.assertEqual(result["reason"], "edit_target_not_found")
        fake_collection.insert_one.assert_not_awaited()


class AddingOnlyUtilityTests(unittest.TestCase):
    def test_parser_keeps_name_and_id(self):
        self.assertEqual(extract_name("Name: Rin Xi\nID: 123"), "Rin Xi")
        self.assertEqual(extract_character_id("Name: Rin Xi\nID: 123"), "123")

    def test_card_edit_text_is_metadata_only(self):
        text = "✏️ Card edited\n🆔 Card ID: 5726\n🪪 Name: Retsu Unahana\n🧩 Anime: Bleach\n💎 Rarity: NOVICE"
        self.assertTrue(_is_metadata_edit(text, None))
        self.assertFalse(_is_metadata_edit(text, {"media_type": "photo"}))

    def test_card_edit_text_parses_with_generic_parser(self):
        result = parse_message(
            "✏️ Card edited\n🆔 Card ID: 5726\n🪪 Name: Retsu Unahana\n🧩 Anime: Bleach\n💎 Rarity: NOVICE"
        )
        self.assertIsNotNone(result)
        self.assertEqual(result.character_id, "5726")
        self.assertEqual(result.name, "Retsu Unahana")
        self.assertEqual(result.anime, "Bleach")
        self.assertEqual(result.rarity, "NOVICE")

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

    def test_deployment_has_no_lookup_settings(self):
        render = Path("render.yaml").read_text(encoding="utf-8")
        for token in (
            "AUTO_LOOKUP_ENABLED", "LOOKUP_IN_PRIVATE", "LOOKUP_IN_GROUPS",
            "LOOKUP_REPLY_NOT_FOUND", "MAX_PHOTO_CANDIDATES",
            "MAX_VIDEO_CANDIDATES",
        ):
            self.assertNotIn(token, render, f"stale lookup setting remains: {token}")

    def test_runtime_state_is_ignored(self):
        gitignore = Path(".gitignore").read_text(encoding="utf-8")
        self.assertIn("addhelper_state.json", gitignore)
        self.assertNotIn("namebotv3/data/*.db", gitignore)

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



class CommonParserRegressionTests(unittest.TestCase):
    def test_hallow_parser_wins_and_returns_one_consistent_result(self):
        result = parse_message(
            "Character Name: Kafka\nRarity: SSR\nID: 77",
            source_key="items_characters_hallow",
        )
        self.assertIsNotNone(result)
        self.assertEqual(result.name, "Kafka")
        self.assertEqual(result.character_id, "77")
        self.assertEqual(result.parser, "hallow")
        self.assertGreaterEqual(result.confidence, 0.99)

    def test_capture_parser(self):
        result = parse_message(
            "🎉 New Character Added\n🎭 Name: Ruan Mei\n🆔 ID: 81",
            source_key="items_capture_character",
        )
        self.assertEqual(result.name, "Ruan Mei")
        self.assertEqual(result.character_id, "81")
        self.assertEqual(result.parser, "capture_character")

    def test_kairo_parser(self):
        result = parse_message(
            "✨ New Card Added\n📛 Character: March 7th\nID: 3",
            source_key="items_kairo_character",
        )
        self.assertEqual(result.name, "March 7th")
        self.assertEqual(result.character_id, "3")
        self.assertEqual(result.parser, "kairo")

    def test_waifux_parser(self):
        result = parse_message(
            "Global Character Info\n➤ Tsunade Senju 🟠\n• Series: Naruto/Boruto\n• ID: 1",
            source_key="items_waifux_grab",
        )
        self.assertEqual(result.name, "Tsunade Senju")
        self.assertEqual(result.character_id, "1")
        self.assertEqual(result.anime, "Naruto/Boruto")
        self.assertEqual(result.parser, "waifux_global")

    def test_owo_numbered_parser(self):
        result = parse_message(
            "OwO! Check out this character!\nAnime\n35: Yoru [👶]\n(SSR)",
            source_key="items_character_catcher",
        )
        self.assertEqual(result.name, "Yoru [👶]")
        self.assertEqual(result.character_id, "35")
        self.assertEqual(result.parser, "character_catcher_owo")

    def test_senpai_parser(self):
        result = parse_message(
            "media + 🎴 Kafka | Limited\n🆔 ID: 42",
            source_key="items_senpai_catcher",
        )
        self.assertEqual(result.name, "Kafka")
        self.assertEqual(result.character_id, "42")
        self.assertEqual(result.rarity, "Limited")
        self.assertEqual(result.parser, "senpai")

    def test_grab_parser_does_not_store_anime_as_name(self):
        result = parse_message(
            "Grab Garden\nHonkai: Star Rail\n1456: Ai Hoshino 👘\n🃏 CATEGORY: Divine",
            source_key="items_waifux_grab",
        )
        self.assertEqual(result.name, "Ai Hoshino 👘")
        self.assertEqual(result.character_id, "1456")
        self.assertEqual(result.parser, "grab_family")

    def test_takers_parser(self):
        result = parse_message(
            "Name: Kafka\nRarity: Mythic\nCharacter ID: 99",
            source_key="items_takers_character",
        )
        self.assertEqual(result.name, "Kafka")
        self.assertEqual(result.character_id, "99")
        self.assertEqual(result.parser, "takers")

    def test_smash_parser(self):
        result = parse_message(
            "Look at this character!\nKafka from Honkai: Star Rail!",
            source_key="items_smash_character",
        )
        self.assertEqual(result.name, "Kafka")
        self.assertEqual(result.anime, "Honkai: Star Rail")
        self.assertEqual(result.parser, "smash_character")

    def test_generic_fallback_works_without_source_knowledge(self):
        result = parse_message(
            "Name: Sparkle\nID: 1234\nRarity: SSR\nAnime: Honkai: Star Rail"
        )
        self.assertEqual(result.name, "Sparkle")
        self.assertEqual(result.character_id, "1234")
        self.assertEqual(result.anime, "Honkai: Star Rail")
        self.assertEqual(result.parser, "generic_structured")

    def test_parser_candidate_list_contains_fallback_and_specialist(self):
        candidates = parse_candidates(
            "Character Name: Kafka\nRarity: SSR\nID: 77",
            source_key="items_characters_hallow",
        )
        self.assertTrue(candidates)
        self.assertEqual(candidates[0].parser, "hallow")
        self.assertIn("generic_structured", {item.parser for item in candidates})

    def test_parser_is_safe_for_unknown_text(self):
        self.assertIsNone(parse_message("hello there, nothing to parse"))
        self.assertEqual(extract_name("hello there, nothing to parse"), None)

    def test_parser_registry_is_explicit(self):
        names = parser_names()
        self.assertEqual(len(names), len(set(names)))
        self.assertIn("generic_structured", names)
        self.assertIn("waifux_global", names)



if __name__ == "__main__":
    unittest.main()
