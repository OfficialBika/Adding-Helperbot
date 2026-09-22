from __future__ import annotations

import re
import unicodedata

LABELS = {
    "name": re.compile(r"(?:character\s+name|char\s+name|name)\s*[:：\-]\s*(.+)", re.I),
}

def norm(text: str | None) -> str:
    text = unicodedata.normalize("NFKC", text or "")
    text = text.replace("\r", "\n")
    text = re.sub(r"[\u200b-\u200f\u2060\ufeff]", "", text)
    return re.sub(r"[ \t]+", " ", text).strip()

def clean_name(value: str) -> str:
    value = re.sub(r"^[^\w\u00c0-\u024f\u0400-\u04ff\u3040-\u30ff\u4e00-\u9fff\uac00-\ud7af]+", "", value)
    value = re.sub(r"\s+", " ", value).strip()
    value = re.sub(r"\s*[-–—|]+\s*(?:rarity|anime|id)\b.*$", "", value, flags=re.I)
    return value.strip("[](){} ")

def extract_name(text: str | None) -> str | None:
    raw = norm(text)
    if not raw:
        return None

    # Strong label forms first.
    for line in raw.splitlines():
        m = re.search(r"(?:character\s+name|char\s+name|name)\s*[:：\-]\s*(.+)$", line, re.I)
        if m:
            name = clean_name(m.group(1))
            if name: return name

    # Common Character Catcher / OwO format: numeric ID followed by name.
    for line in raw.splitlines():
        m = re.match(r"^\s*(?:ID\s*)?(\d+)\s*[:：\-]\s*(.+?)\s*$", line, re.I)
        if m:
            name = clean_name(m.group(2))
            if name and not re.search(r"^(?:anime|rarity|id)\b", name, re.I):
                return name

    # Common database line: ID / Name / Movie.
    for line in raw.splitlines():
        parts = [p.strip() for p in line.split("/")]
        if len(parts) >= 2 and parts[0].isdigit():
            name = clean_name(parts[1])
            if name: return name

    # Some sources put a standalone "Name - ..." line.
    for line in raw.splitlines():
        m = re.match(r"^\s*name\s*[-–—]\s*(.+)$", line, re.I)
        if m:
            name = clean_name(m.group(1))
            if name: return name

    return None
