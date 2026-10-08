"""Characters Hallow parser."""

from __future__ import annotations

import re

from .base import CharacterParser, ParsedCharacter, clean_value, norm


class HallowParser(CharacterParser):
    name = "hallow"
    priority = 99
    source_keys = frozenset({"items_characters_hallow"})

    @classmethod
    def parse(cls, text: str) -> ParsedCharacter | None:
        raw = norm(text)
        if not raw or not re.search(r"\bCharacter\s*Name\s*[:：]", raw, re.I):
            return None

        name_match = re.search(r"(?im)^\s*Character\s*Name\s*[:：]\s*(.+?)\s*$", raw)
        id_match = re.search(r"(?im)^\s*ID\s*[:：-]\s*(\d+)\s*$", raw)
        rarity_match = re.search(r"(?im)^\s*Rarity\s*[:：-]\s*(.+?)\s*$", raw)

        if not name_match:
            return None
        return cls.make(
            name=name_match.group(1),
            id=int(id_match.group(1)) if id_match else None,
            rarity=rarity_match.group(1) if rarity_match else None,
            confidence=0.995 if id_match else 0.96,
            matched_fields=(
                ("name", "id", "rarity") if id_match and rarity_match else
                ("name", "id") if id_match else ("name",)
            ),
            raw=raw,
        )
