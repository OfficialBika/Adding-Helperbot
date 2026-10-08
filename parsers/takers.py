"""Takers (/take) parser."""

from __future__ import annotations

import re

from .base import CharacterParser, ParsedCharacter, clean_value, norm


class TakersParser(CharacterParser):
    name = "takers"
    priority = 92
    source_keys = frozenset({"items_takers_character"})

    @classmethod
    def parse(cls, text: str) -> ParsedCharacter | None:
        raw = norm(text)
        if not raw:
            return None

        name = re.search(r"(?im)^\s*Name\s*[:：-]\s*(.+?)\s*$", raw)
        cid = re.search(r"(?im)^\s*Character\s*ID\s*[:：-]\s*(\d+)\s*$", raw)
        if not name or not cid:
            return None

        rarity = re.search(r"(?im)^\s*Rarity\s*[:：-]\s*(.+?)\s*$", raw)
        return cls.make(
            name=name.group(1),
            id=int(cid.group(1)),
            rarity=clean_value(rarity.group(1)) if rarity else None,
            confidence=0.98,
            matched_fields=("name", "id", "rarity") if rarity else ("name", "id"),
            raw=raw,
        )
