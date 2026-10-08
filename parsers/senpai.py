"""Senpai catcher parser."""

from __future__ import annotations

import re

from .base import CharacterParser, ParsedCharacter, clean_name, clean_value, norm


class SenpaiParser(CharacterParser):
    name = "senpai"
    priority = 94
    source_keys = frozenset({"items_senpai_catcher", "items_character_picker"})

    @classmethod
    def parse(cls, text: str) -> ParsedCharacter | None:
        raw = norm(text)
        if not raw:
            return None

        strong = re.search(
            r"(?im)^\s*(?:media\s*\+\s*)?🎴\s*(.+?)\s*\|\s*(.+?)\s*$",
            raw,
            re.I,
        )
        valuation = re.search(r"⚖️\s*character\s+valuation.*?🎴\s*name\s*:", raw, re.I | re.S)
        header = bool(
            strong
            or valuation
            or re.search(r"new\s+character\s+added\s+to\s+the\s+bot", raw, re.I)
        )
        if not header:
            return None

        name = clean_name(strong.group(1)) if strong else None
        rarity = clean_value(strong.group(2)) if strong else None
        if not name:
            match = re.search(r"(?im)^\s*Name\s*[:：-]\s*(.+?)\s*$", raw)
            if match:
                name = clean_name(match.group(1))
        if not name:
            return None

        mid = re.search(
            r"(?im)^\s*[🆔🔢#](?:\ufe0f)?\s*(?:ID\s*)?[:：-]\s*(\d+)\s*$",
            raw,
        )
        if not mid:
            mid = re.search(r"(?im)^\s*ID\s*[:：-]\s*(\d+)\s*$", raw)

        return cls.make(
            name=name,
            id=int(mid.group(1)) if mid else None,
            rarity=rarity,
            confidence=0.97 if mid else 0.92,
            matched_fields=("header", "name", "id") if mid else ("header", "name"),
            raw=raw,
        )
