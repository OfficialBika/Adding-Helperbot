from unified.parser import extract_character_id, extract_name


def test_waifux_global_character_info():
    text = """Media + ❖ Global Character Info ❖

➤ Tsunade Senju 🟠
• Series: Naruto/Boruto
• ID: 1
"""
    assert extract_character_id(text) == "1"
    assert extract_name(text) == "Tsunade Senju"


def test_waifux_global_info_keeps_name_punctuation():
    text = """Media + ❖ Global Character Info ❖
➤ Oshi no Ko: Ai Hoshino 🟠
• Series: Oshi no Ko
• ID: 42
"""
    assert extract_character_id(text) == "42"
    assert extract_name(text) == "Oshi no Ko: Ai Hoshino"
