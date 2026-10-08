"""WaifuxGrabBot Global Character Info parser."""

from __future__ import annotations

import re
import unicodedata

from .base import CharacterParser, ParsedCharacter, clean_name, clean_value, norm


class WaifuxParser(CharacterParser):
    name = "waifux_global"
    priority = 98
    source_keys = frozenset({"items_waifux_grab"})

    @classmethod
    def parse(cls, text: str) -> ParsedCharacter | None:
        raw = norm(text)
        if not re.search(r"global\s+character\s+info", raw, re.I):
            return None

        name_match = re.search(r"(?m)^\s*➤\s*(.+?)\s*$", raw)
        if not name_match:
            name_match = re.search(r"(?im)^\s*Name\s*[:：-]\s*(.+?)\s*$", raw)
        if not name_match:
            return None

        name = name_match.group(1).strip()
        while name:
            last = name[-1]
            if last in "\ufe0f\u200d\u20e3" or unicodedata.category(last) in {"So", "Sk"}:
                name = name[:-1].rstrip()
                continue
            break
        name = clean_name(name)

        cid = re.search(
            r"(?im)^\s*[•●▪️🔹🔸\-*–—]?\s*(?:🆔\ufe0f?\s*)?(?:Character\s*)?ID\s*[:：=-]\s*\`?(\d+)\`?\s*$",
            raw,
        )
        series = re.search(r"(?im)^\s*[•●▪️🔹🔸\-*–—]?\s*Series\s*[:：-]\s*(.+?)\s*$", raw)
        rarity = re.search(r"(?im)^\s*[•●▪️🔹🔸\-*–—]?\s*Rarity\s*[:：-]\s*(.+?)\s*$", raw)

        return cls.make(
            name=name,
            id=int(cid.group(1)) if cid else None,
            anime=clean_value(series.group(1)) if series else None,
            rarity=clean_value(rarity.group(1)) if rarity else None,
            confidence=0.995 if cid else 0.96,
            matched_fields=("header", "name", "id") if cid else ("header", "name"),
            raw=raw,
        )
