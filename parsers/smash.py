"""Smash Character parser."""

from __future__ import annotations

import re

from .base import CharacterParser, ParsedCharacter, clean_name, norm


class SmashParser(CharacterParser):
    name = "smash_character"
    priority = 90
    source_keys = frozenset({"items_smash_character"})

    @classmethod
    def parse(cls, text: str) -> ParsedCharacter | None:
        raw = norm(text)
        match = re.search(
            r"look\s+at\s+this\s+character\s*[!！:：-]?\s*(?:\n|\s)+(.+?)\s+from\s+(.+?)(?:!|！|\n|$)",
            raw,
            re.I | re.S,
        )
        if not match:
            return None
        name = clean_name(match.group(1))
        if not name:
            return None
        return cls.make(
            name=name,
            anime=match.group(2),
            confidence=0.94,
            matched_fields=("header", "name", "anime"),
            raw=raw,
        )
