import unittest
from types import SimpleNamespace

from unified.parser import extract_character_id, extract_name
from services.source_resolver import grabber_source_variant, resolve_source_collection
from unified.store import _index_source_variant


CAPTURE_TEXT = """Media + ✨ New Character Added!

🎭 Name   Anya Forger
📺 Anime  Spy X Family
⭐ Rarity 🫧 Premium
💰 Price  79,823 coins
🆔 ID     1368
👤 By     複|•ᴅᴏғʟᴀᴍɪɴɢᴏ•ツ
"""

HUSBANDO_TEXT = """Media + OwO! Check out this husbando!

Naruto / Boruto
10895: Rock Lee [👘]
(🔮𝙍𝘼𝙍𝙄𝙏𝙔:  Limited Edition)

👘𝑲𝒊𝒎𝒐𝒏𝒐👘

➼ ᴀᴅᴅᴇᴅ ʙʏ: Amiya
"""

WAIFU_TEXT = """Media + OwO! Check out this waifu!

Honkai Series
20079: Pearl [🚓]
(🔮𝙍𝘼𝙍𝙄𝙏𝙔:  Limited Edition)

🚓𝑶𝒇𝒇𝒊𝒄𝒆𝒓🚓

➼ ᴀᴅᴅᴇᴅ ʙʏ: Amiya
"""


class ParserRegressionTests(unittest.TestCase):
    def test_capture_name_and_id_ignore_by_line(self):
        self.assertEqual(extract_name(CAPTURE_TEXT), "Anya Forger")
        self.assertEqual(extract_character_id(CAPTURE_TEXT), "1368")

    def test_grabber_names_keep_closing_bracket(self):
        self.assertEqual(extract_name(HUSBANDO_TEXT), "Rock Lee [👘]")
        self.assertEqual(extract_character_id(HUSBANDO_TEXT), "10895")
        self.assertEqual(extract_name(WAIFU_TEXT), "Pearl [🚓]")
        self.assertEqual(extract_character_id(WAIFU_TEXT), "20079")

    def test_catcher_log_names_keep_closing_bracket(self):
        text = """Character image updated for Character Rock Lee [👘]
"""
        self.assertEqual(extract_name(text), "Rock Lee [👘]")

    def test_common_labeled_names_keep_bracket_suffix(self):
        samples = [
            ("Name: Pearl [🚓]\nID: 20079", "Pearl [🚓]"),
            ("📛 Name: Yoru [👶]\n⭐ Rarity: Rare", "Yoru [👶]"),
            ("Character: Noelle Silva [👠]\nID: 621", "Noelle Silva [👠]"),
        ]
        for text, expected in samples:
            with self.subTest(expected=expected):
                self.assertEqual(extract_name(text), expected)


class GrabberSourceRegressionTests(unittest.TestCase):
    def _message(self, text):
        return SimpleNamespace(
            caption=text,
            text=None,
            html_text=None,
            md_text=None,
            external_reply=None,
            reply_to_message=None,
            forward_origin=None,
            forward_from_chat=None,
            sender_chat=None,
            via_bot=None,
            forward_from=None,
            from_user=SimpleNamespace(id=None, is_bot=False, username=None),
        )

    def test_both_grabbers_use_one_fw_collection(self):
        husbando = self._message(HUSBANDO_TEXT)
        waifu = self._message(WAIFU_TEXT)
        self.assertEqual(resolve_source_collection(husbando), "items_grabber_fw")
        self.assertEqual(resolve_source_collection(waifu), "items_grabber_fw")
        self.assertEqual(grabber_source_variant(husbando), "husbando_grabber")
        self.assertEqual(grabber_source_variant(waifu), "waifu_grabber")

    def test_stylized_admin_signatures_identify_each_grabber(self):
        waifu = self._message("some grabber card")
        waifu.forward_origin = SimpleNamespace(
            author_signature="˹ᴡᴀɪғᴜ ɢꝛᴀʙʙᴇʀ ʙᴏᴛ˼ 🫧",
            chat=SimpleNamespace(id=-1001, username="Grabber_Database", title="Grabber Database"),
            sender_user=None,
            sender_user_name=None,
            message_id=123,
        )
        husbando = self._message("some grabber card")
        husbando.forward_origin = SimpleNamespace(
            author_signature="˹ʜᴜsʙᴀɴᴅᴏ ɢꝛᴀʙʙᴇʀ ʙᴏᴛ˼ 🥤",
            chat=SimpleNamespace(id=-1001, username="Grabber_Database", title="Grabber Database"),
            sender_user=None,
            sender_user_name=None,
            message_id=124,
        )
        self.assertEqual(grabber_source_variant(waifu), "waifu_grabber")
        self.assertEqual(grabber_source_variant(husbando), "husbando_grabber")


    def test_generic_admin_signature_does_not_create_id_identity(self):
        msg = self._message("some grabber card")
        msg.forward_origin = SimpleNamespace(
            author_signature="Shared Admin",
            chat=SimpleNamespace(id=-1001, username="Grabber_Database", title="Grabber Database"),
            sender_user=None,
            sender_user_name=None,
            message_id=123,
        )
        self.assertEqual(grabber_source_variant(msg), None)

    def test_unknown_grabber_identity_stays_unknown(self):
        msg = self._message("Media + OwO! Check out this character!\n42: Same")
        self.assertEqual(grabber_source_variant(msg), None)

    def test_index_variant_keeps_known_grabber_identity_separate(self):
        self.assertEqual(
            _index_source_variant("items_grabber_fw", "waifu_grabber", file_unique_id="UID1"),
            "waifu_grabber",
        )
        self.assertEqual(
            _index_source_variant("items_grabber_fw", "husbando_grabber", file_unique_id="UID2"),
            "husbando_grabber",
        )

    def test_unknown_grabber_index_variant_is_media_scoped(self):
        self.assertEqual(
            _index_source_variant("items_grabber_fw", None, file_unique_id="UID-42"),
            "unknown_uid:UID-42",
        )
        self.assertNotEqual(
            _index_source_variant("items_grabber_fw", None, file_unique_id="UID-42"),
            _index_source_variant("items_grabber_fw", None, file_unique_id="UID-43"),
        )

    def test_normal_source_keeps_variant_unchanged(self):
        self.assertIsNone(
            _index_source_variant("items_character_catcher", None, file_unique_id="UID1")
        )


if __name__ == "__main__":
    unittest.main()
