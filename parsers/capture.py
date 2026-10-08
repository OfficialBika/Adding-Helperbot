"""CaptureCharacterBot parser."""

from __future__ import annotations

import re

from .base import CharacterParser, ParsedCharacter, clean_value, norm


class CaptureParser(CharacterParser):
    name = "capture_character"
    priority = 97
    source_keys = frozenset({"items_capture_character"})

    @classmethod
    def parse(cls, text: str) -> ParsedCharacter | None:
        raw = norm(text)
        if not re.search(r"new\s+character\s+added", raw, re.I):
            return None

        name = re.search(r"(?im)^\s*🎭\s*Name\s*[:：-]?\s*(.+?)\s*$", raw)
        if not name:
            name = re.search(r"(?im)^\s*(?:📛|👤)?\s*Name\s*[:：-]\s*(.+?)\s*$", raw)
        if not name:
            return None

        cid = re.search(r"(?im)^\s*🆔(?:\ufe0f)?\s*ID\s*[:：-]?\s*(\d+)\s*$", raw)
        if not cid:
            cid = re.search(r"(?im)^\s*(?:Character\s*)?ID\s*[:：-]\s*(\d+)\s*$", raw)
        rarity = re.search(r"(?im)^\s*(?:⭐\s*)?Rarity\s*[:：-]\s*(.+?)\s*$", raw)

        return cls.make(
            name=clean_value(name.group(1)),
            id=int(cid.group(1)) if cid else None,
            rarity=rarity.group(1) if rarity else None,
            confidence=0.99 if cid else 0.96,
            matched_fields=("header", "name", "id") if cid else ("header", "name"),
            raw=raw,
        )
