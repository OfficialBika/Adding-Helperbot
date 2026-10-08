"""Source-neutral fallback parser.

This parser intentionally requires structured evidence. It is the last
candidate so a weak generic match cannot override a stronger source parser.
"""

from __future__ import annotations

import re

from .base import CharacterParser, ParsedCharacter, clean_name, clean_value, labelled_fields, norm, numbered_line, numeric_id


class GenericParser(CharacterParser):
    name = "generic_structured"
    priority = 10

    @classmethod
    def parse(cls, text: str) -> ParsedCharacter | None:
        raw = norm(text)
        if not raw:
            return None

        fields = labelled_fields(raw)
        name = fields.get("name")
        cid = numeric_id(fields.get("id"))

        if name:
            matched = ["name"]
            confidence = 0.82
            if cid is not None:
                matched.append("id")
                confidence = 0.90
            if fields.get("anime"):
                matched.append("anime")
                confidence += 0.02
            if fields.get("rarity"):
                matched.append("rarity")
                confidence += 0.02
            return cls.make(
                name=name,
                id=cid,
                anime=fields.get("anime"),
                rarity=fields.get("rarity"),
                confidence=min(confidence, 0.94),
                matched_fields=tuple(matched),
                raw=raw,
            )

        numbered = numbered_line(raw)
        if numbered:
            number, candidate = numbered
            # A bare numeric/name line is useful fallback evidence, but
            # deliberately carries a lower confidence than labelled cards.
            if not re.match(r"^(?:anime|series|rarity|id|role)\b", candidate, re.I):
                return cls.make(
                    name=clean_name(candidate),
                    id=number,
                    confidence=0.78,
                    matched_fields=("name", "id"),
                    raw=raw,
                )

        # Common slash-delimited archive format: 123 / Name / Anime
        for line in raw.splitlines():
            match = re.match(r"^\s*(\d+)\s*/\s*([^/]+?)(?:\s*/\s*(.+?))?\s*$", line)
            if match:
                name = clean_name(match.group(2))
                if not name:
                    continue
                return cls.make(
                    name=name,
                    id=int(match.group(1)),
                    anime=clean_value(match.group(3)),
                    confidence=0.80,
                    matched_fields=("name", "id") if not match.group(3) else ("name", "id", "anime"),
                    raw=raw,
                )

        return None
