from __future__ import annotations

import re
import unicodedata
from dataclasses import dataclass
from typing import ClassVar

NOISE_RE = re.compile(
    r"(?:new\s+(?:character|waifu|husbando)\s+added|"
    r"added\s+new\s+character|uploaded\s*\(/?li\)|"
    r"artwork\s+updated|rarity\s+updated|role\s+updated|"
    r"character\s+updated|global\s+owners|globally\s+catches|"
    r"added\s+by|uploader|photo\s+updated|leave\s+a\s+comment|"
    r"comments?\b)",
    re.I,
)

LABELS: dict[str, str] = {
    "name": r"(?:character\s*name|char\s*name|character|name)",
    "id": r"(?:character\s*)?id|item\s*id|card\s*id",
    "anime": r"(?:anime|series|movie)",
    "rarity": r"rarity",
    "role": r"role",
}


@dataclass(frozen=True, slots=True)
class ParsedCharacter:
    name: str | None = None
    id: int | None = None
    rarity: str | None = None
    anime: str | None = None
    parser: str = ""
    confidence: float = 0.0
    matched_fields: tuple[str, ...] = ()
    raw: str = ""

    @property
    def character_id(self) -> str | None:
        return str(self.id) if self.id is not None else None

    @property
    def is_valid(self) -> bool:
        return bool(self.name)


class CharacterParser:
    name: ClassVar[str] = "base"
    priority: ClassVar[int] = 0
    source_keys: ClassVar[frozenset[str]] = frozenset()

    @classmethod
    def parse(cls, text: str) -> ParsedCharacter | None:
        raise NotImplementedError

    @classmethod
    def make(
        cls,
        *,
        name: str | None,
        id: int | None = None,
        rarity: str | None = None,
        anime: str | None = None,
        confidence: float = 0.0,
        matched_fields: tuple[str, ...] = (),
        raw: str = "",
    ) -> ParsedCharacter | None:
        name = clean_name(name)
        if not name:
            return None
        return ParsedCharacter(
            name=name,
            id=id,
            rarity=clean_value(rarity),
            anime=clean_value(anime),
            parser=cls.name,
            confidence=max(0.0, min(1.0, float(confidence))),
            matched_fields=tuple(matched_fields),
            raw=raw,
        )


def norm(text: str | None) -> str:
    value = unicodedata.normalize("NFKC", text or "")
    value = value.replace("\r", "\n")
    value = re.sub(r"[\u200b-\u200f\u2060\ufeff]", "", value)
    return re.sub(r"[ \t]+", " ", value).strip()


def clean_value(value: str | None) -> str | None:
    value = norm(value)
    if not value:
        return None
    value = re.sub(r"^\s*\`+(.*?)\`+\s*$", r"\1", value, flags=re.S).strip()
    return value.strip(" |•:：-–—")


def clean_name(value: str | None) -> str | None:
    value = clean_value(value)
    if not value:
        return None
    value = re.sub(r"^(?:📛|👤|🆔|⭐|💠|🎬|🎭|📤)+\s*", "", value)
    value = re.sub(
        r"^(?:name|character\s*name|char\s*name)\s*[:：•\-=]\s*",
        "",
        value,
        flags=re.I,
    )
    value = re.split(
        r"\s*(?:\||•)\s*(?:anime|movie|series|rarity|role|id)\b",
        value,
        maxsplit=1,
        flags=re.I,
    )[0]
    value = re.sub(
        r"\s*[-–—|]+\s*(?:rarity|anime|id|role)\b.*$",
        "",
        value,
        flags=re.I,
    )
    value = re.sub(
        r"^[^\w\u00c0-\u024f\u0400-\u04ff\u3040-\u30ff\u4e00-\u9fff\uac00-\ud7af]+",
        "",
        value,
    )
    value = value.strip(" |•:：-–—")
    value = re.sub(r"\s+", " ", value).strip()
    return value or None


def line_field(text: str, label: str) -> str | None:
    pattern = re.compile(
        rf"^\s*[^\w\n\r:：•\-=]{{0,8}}(?:{label})\s*[:：•\-=]\s*(.+?)\s*$",
        re.I,
    )
    for line in norm(text).splitlines():
        match = pattern.search(line)
        if match:
            value = clean_value(match.group(1))
            if value:
                return value
    return None


def labelled_fields(text: str) -> dict[str, str]:
    result: dict[str, str] = {}
    raw = norm(text)
    for line in raw.splitlines():
        for key, label in LABELS.items():
            if key in result:
                continue
            value = line_field(line, label)
            if value:
                result[key] = value
    return result


def numeric_id(value: str | None) -> int | None:
    if not value:
        return None
    match = re.search(r"\d+", str(value))
    return int(match.group(0)) if match else None


def numbered_line(text: str) -> tuple[int, str] | None:
    for line in norm(text).splitlines():
        match = re.match(
            r"^\s*[「『【\[\(]?\s*(?:🆔\ufe0f?\s*)?(\d+)\s*[:：-]\s*(.+?)\s*[」』】\]\)]?\s*$",
            line,
        )
        if match:
            name = clean_name(match.group(2))
            if name:
                return int(match.group(1)), name
    return None
