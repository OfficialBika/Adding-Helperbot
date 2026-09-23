from __future__ import annotations

import re
import unicodedata


# This parser deliberately stores only the character name.  ID/anime/rarity are
# used only as parsing boundaries and are never persisted by unified/store.py.

LABEL_ALIASES = {
    "name": r"(?:character\s*name|char\s*name|character|name)",
    "anime": r"(?:anime|series|movie)",
    "id": r"(?:character\s*)?id|item\s*id|card\s*id",
    "rarity": r"rarity",
    "role": r"role",
}

NOISE_RE = re.compile(
    r"(?:new\s+(?:character|waifu|husbando)\s+added|"
    r"added\s+new\s+character|"
    r"uploaded\s*\(/?li\)|"
    r"artwork\s+updated|rarity\s+updated|role\s+updated|"
    r"character\s+updated|global\s+owners|globally\s+catches|"
    r"added\s+by|uploader|photo\s+updated|leave\s+a\s+comment|"
    r"comments?\b)",
    re.I,
)


def norm(text: str | None) -> str:
    text = unicodedata.normalize("NFKC", text or "")
    text = text.replace("\r", "\n")
    text = re.sub(r"[\u200b-\u200f\u2060\ufeff]", "", text)
    return re.sub(r"[ \t]+", " ", text).strip()


def strip_symbols(value: str) -> str:
    value = value.strip()
    value = re.sub(r"^[^\w\u00c0-\u024f\u0400-\u04ff\u3040-\u30ff\u4e00-\u9fff\uac00-\ud7af]+", "", value)
    return value.strip("[](){}<>|•:：-–—")


def clean_name(value: str) -> str:
    value = norm(value)
    value = re.sub(r"^(?:📛|👤|🆔|⭐|💠|🎬|🎭|📤)+\s*", "", value)
    value = re.sub(r"^(?:name|character\s*name|char\s*name)\s*[:：•\-=]\s*", "", value, flags=re.I)
    # Never let adjacent metadata become part of the stored name.
    value = re.split(
        r"\s*(?:\||•)\s*(?:anime|movie|series|rarity|role|id)\b",
        value,
        maxsplit=1,
        flags=re.I,
    )[0]
    value = re.sub(r"\s*[-–—|]+\s*(?:rarity|anime|id|role)\b.*$", "", value, flags=re.I)
    value = strip_symbols(value)
    return re.sub(r"\s+", " ", value).strip() or None


def _label_value(text: str, label: str) -> str | None:
    pat = re.compile(
        rf"(?:^|[\n\r\s])[^\w\n\r:：•\-=]{{0,8}}{label}\s*[:：•\-=]\s*(.+?)"
        rf"(?=\s+[^\w\n\r:：•\-=]{{0,8}}(?:{LABEL_ALIASES['id']}|{LABEL_ALIASES['name']}|{LABEL_ALIASES['anime']}|{LABEL_ALIASES['rarity']}|{LABEL_ALIASES['role']})\s*[:：•\-=]|$)",
        re.I | re.S,
    )
    m = pat.search(text)
    return clean_name(m.group(1)) if m else None


def _line_label_value(line: str, label: str) -> str | None:
    m = re.search(rf"(?:[^\w\n\r:：•\-=]{{0,8}}){label}\s*[:：•\-=]\s*(.+?)\s*$", line, re.I)
    return clean_name(m.group(1)) if m else None


def _myanmar_name(text: str) -> str | None:
    for line in norm(text).splitlines():
        line = line.strip()
        if not line:
            continue
        v = _line_label_value(line, r"(?:📛\s*)?Name")
        if v:
            return v
    # Icon-only name line used by some Super Zeko / uploaded formats.
    for line in norm(text).splitlines():
        line = line.strip()
        if not line or NOISE_RE.search(line):
            continue
        if re.match(r"^📛\s*.+", line):
            return clean_name(line)
    return None


def _senpai_name(text: str) -> str | None:
    for line in norm(text).splitlines():
        v = _line_label_value(line, r"(?:👤\s*)?NAME")
        if v:
            return v.upper() if re.search(r"[A-Za-z]", v) else v
    return None


def _smash_name(text: str) -> str | None:
    raw = norm(text)
    m = re.search(
        r"look\s+at\s+this\s+character\s*(?:\n|\s)+(.+?)\s+from\s+(.+?)(?:!|！|\n|$)",
        raw,
        re.I | re.S,
    )
    if m:
        return clean_name(m.group(1))
    for line in raw.splitlines():
        m = re.match(r"^(.+?)\s+from\s+(.+?)(?:!|！)?$", line.strip(), re.I)
        if m:
            return clean_name(m.group(1))
    return None


def extract_character_id(text: str | None) -> str | None:
    """Return the source character ID when the source format exposes one.

    IDs are persisted as lookup identity, not as display metadata. Source
    specific formats are handled conservatively so an unrelated number in
    prose is never treated as a character ID.
    """
    raw = norm(text)
    if not raw:
        return None

    # Explicit ID labels are unambiguous.
    for line in raw.splitlines():
        m = re.match(
            rf"^\s*(?:[^\w\n\r:：•\-=]{{0,8}})?{LABEL_ALIASES['id']}\s*[:：•\-=]\s*(\d+)\s*$",
            line.strip(),
            re.I,
        )
        if m:
            return m.group(1)

    # OwO inline result: "123: Name [emoji]". Only inspect lines that look
    # like the character-entry shape; anime/rarity lines are ignored.
    if re.search(r"media\s*\+\s*owo!\s*check\s+out\s+this\s+character", raw, re.I):
        for line in raw.splitlines():
            m = re.match(r"^\s*(\d+)\s*[:：-]\s*.+?\s*$", line)
            if m:
                return m.group(1)

    # Database format: ID / Name / Movie.
    for line in raw.splitlines():
        m = re.match(r"^\s*(\d+)\s*/\s*[^/]+(?:/|$)", line)
        if m:
            return m.group(1)

    return None

def extract_name(text: str | None) -> str | None:
    raw = norm(text)
    if not raw:
        return None

    # Source-specific formats first because their boundaries are strongest.
    for parser in (_senpai_name, _myanmar_name, _smash_name):
        name = parser(raw)
        if name:
            return name

    # Explicit Name/Character Name labels, including emoji-prefixed labels.
    for line in raw.splitlines():
        for label in (
            LABEL_ALIASES["name"],
            r"(?:📛\s*)?Name",
            r"(?:👤\s*)?NAME",
        ):
            value = _line_label_value(line, label)
            if value:
                return value

    value = _label_value(raw, LABEL_ALIASES["name"])
    if value:
        return value

    # OwO inline result: "123: Name [emoji]". The numeric ID and bracketed
    # rarity/element marker are parsing-only and are never stored.
    if re.search(r"media\s*\+\s*owo!\s*check\s+out\s+this\s+character", raw, re.I):
        for line in raw.splitlines():
            line = line.strip()
            m = re.match(r"^(?:ID\s*)?(\d+)\s*[:：-]\s*(.+?)\s*$", line, re.I)
            if not m:
                continue
            value = re.sub(r"\s+\[[^\]]*\]\s*$", "", m.group(2)).strip()
            value = clean_name(value)
            if value and not re.match(r"^(?:anime|rarity|id|role)\\b", value, re.I):
                return value

    # OwO-style: numeric ID followed by character name.
    for line in raw.splitlines():
        line = line.strip()
        m = re.match(r"^(?:ID\s*)?(\d+)\s*[:：\-]\s*(.+?)\s*$", line, re.I)
        if m:
            value = clean_name(m.group(2))
            if value and not re.match(r"^(?:anime|rarity|id|role)\b", value, re.I):
                return value

        m = re.match(r"^(?:ID\s*)?(\d+)\s+(.+?)\s*$", line, re.I)
        if m:
            value = clean_name(m.group(2))
            if value and not NOISE_RE.search(value):
                return value

    # Database format: ID / Name / Movie.
    for line in raw.splitlines():
        parts = [p.strip() for p in line.split("/")]
        if len(parts) >= 2 and parts[0].isdigit():
            value = clean_name(parts[1])
            if value:
                return value

    # "Name - ..." fallback.
    for line in raw.splitlines():
        m = re.match(r"^\s*(?:📛\s*)?name\s*[-–—:]\s*(.+)$", line, re.I)
        if m:
            value = clean_name(m.group(1))
            if value:
                return value

    return None
