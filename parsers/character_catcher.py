"""Character Catcher / Picker-style OwO parser."""

from __future__ import annotations

import re

from .base import CharacterParser, ParsedCharacter, clean_name, norm


class CharacterCatcherParser(CharacterParser):
    name = "character_catcher_owo"
    priority = 96
    source_keys = frozenset({"items_character_catcher", "items_character_catcher_fw", "items_character_picker"})

    @classmethod
    def parse(cls, text: str) -> ParsedCharacter | None:
        raw = norm(text)
        if not raw:
            return None

        owo_header = re.search(
            r"owo!\s*check\s+out\s+this\s+(?:character|waifu|husbando|update)",
            raw,
            re.I,
        )
        log_event = re.search(
            r"(?:new\s+name|(?:changed\s+event|updated\s+image|character\s+image\s+updated)\s+for\s+character|added\s+new\s+character)",
            raw,
            re.I,
        )
        if not owo_header and not log_event:
            return None

        new_name = re.search(r"(?im)^\s*New\s+Name\s*[:：]\s*(.+?)\s*$", raw)
        if new_name:
            name = clean_name(new_name.group(1))
            if name:
                return cls.make(name=name, confidence=0.98, matched_fields=("event", "name"), raw=raw)

        event_name = re.search(
            r"\b(?:changed\s+event\s+for|updated\s+image\s+for|character\s+image\s+updated\s+for)\s+Character\s+(.+?)(?:\n|$)",
            raw,
            re.I,
        )
        if event_name:
            name = clean_name(event_name.group(1))
            if name:
                return cls.make(name=name, confidence=0.97, matched_fields=("event", "name"), raw=raw)

        numbered = re.search(
            r"(?m)^\s*[「『【\[\(]?\s*(?:🆔\ufe0f?\s*)?(\d+)\s*[:：-]\s*(.+?)\s*$",
            raw,
            re.I,
        )
        if numbered:
            name = clean_name(numbered.group(2))
            if name:
                return cls.make(
                    name=name,
                    id=int(numbered.group(1)),
                    confidence=0.99 if owo_header else 0.94,
                    matched_fields=("header", "name", "id") if owo_header else ("event", "name", "id"),
                    raw=raw,
                )

        added = re.search(r"\badded\s+new\s+Character[ \t]+(.+?)(?:\n|$)", raw, re.I)
        if added:
            candidate = clean_name(added.group(1))
            if candidate and not re.fullmatch(r"\((?:video|photo|animation|document|media)\)", candidate, re.I):
                return cls.make(name=candidate, confidence=0.93, matched_fields=("event", "name"), raw=raw)

        update = re.search(
            r"(?m)^\s*[「『【\[\(]?\s*ID\s*[:：-]\s*(\d+)\s+(.+?)\s*[」』】\]\)]?\s*$",
            raw,
            re.I,
        )
        if update and owo_header:
            return cls.make(
                name=clean_name(update.group(2)),
                id=int(update.group(1)),
                confidence=0.98,
                matched_fields=("header", "name", "id"),
                raw=raw,
            )

        return None
