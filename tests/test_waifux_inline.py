import unittest

from unified.parser import extract_character_id, extract_name


class WaifuxInlineParserTests(unittest.TestCase):
    def test_global_character_info(self):
        text = """Media + ❖ Global Character Info ❖

➤ Tsunade Senju 🟠
• Series: Naruto/Boruto
• ID: 1
"""
        self.assertEqual(extract_character_id(text), "1")
        self.assertEqual(extract_name(text), "Tsunade Senju")

    def test_global_info_keeps_name_punctuation(self):
        text = """Media + ❖ Global Character Info ❖
➤ Oshi no Ko: Ai Hoshino 🟠
• Series: Oshi no Ko
• ID: 42
"""
        self.assertEqual(extract_character_id(text), "42")
        self.assertEqual(extract_name(text), "Oshi no Ko: Ai Hoshino")

    def test_global_info_drops_rarity_and_status_suffix(self):
        text = """Media + ❖ Global Character Info ❖
➤ Noelle Silva 🔵 [👠]
• Series: Black Clover
• ID: 621
"""
        self.assertEqual(extract_character_id(text), "621")
        self.assertEqual(extract_name(text), "Noelle Silva")


if __name__ == "__main__":
    unittest.main()
