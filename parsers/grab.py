"""Grab/Garden/Grabber source parser."""

from __future__ import annotations

import re

from .base import CharacterParser, ParsedCharacter, clean_name, norm


class GrabParser(CharacterParser):
    name = "grab_family"
    priority = 93
    source_keys = frozenset({
        "items_grabber_fw",
        "items_husbando_grabber",
        "items_grab_your_waifu",
        "items_grab_your_husbando",
        "items_waifux_grab",
        "items_waifu_grabber",
    })

    @classmethod
    def parse(cls, text: str) -> ParsedCharacter | None:
        raw = norm(text)
        if not raw:
            return None

        grab_header = re.search(
            r"(?:owo!\s*check\s+out\s+this\s+(?:husbando|waifu)|global\s+character\s+info|grab\s+garden)",
            raw,
            re.I,
        )
        numbered = re.search(r"(?m)^\s*(\d+)\s*[:：-]\s*(.+?)\s*$", raw)

        if numbered and (
            grab_header
            or re.search(r"\b(?:CATEGORY|DIVINE|COMMON|RARE|LEGENDARY)\b", raw, re.I)
        ):
            name = clean_name(numbered.group(2))
            if name:
                category = re.search(r"\bCATEGORY\s*[:：]\s*(.+)", raw, re.I)
                rarity = f"🃏 {category.group(1).strip()}" if category else None
                return cls.make(
                    name=name,
                    id=int(numbered.group(1)),
                    rarity=rarity,
                    confidence=0.98 if grab_header else 0.91,
                    matched_fields=("header", "name", "id") if grab_header else ("name", "id"),
                    raw=raw,
                )

        if grab_header:
            name_match = re.search(r"(?im)^\s*(?:📛|👤)?\s*Name\s*[:：-]\s*(.+?)\s*$", raw)
            id_match = re.search(r"(?im)^\s*(?:🆔\ufe0f?\s*)?(?:Character\s*)?ID\s*[:：-]\s*(\d+)\s*$", raw)
            if name_match:
                return cls.make(
                    name=clean_name(name_match.group(1)),
                    id=int(id_match.group(1)) if id_match else None,
                    confidence=0.94 if id_match else 0.86,
                    matched_fields=("header", "name", "id") if id_match else ("header", "name"),
                    raw=raw,
                )

        return None
