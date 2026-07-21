"""Senpai (/pick) parser."""
import re
from .base import ParsedCharacter

def parse(text: str) -> ParsedCharacter:
    text = text or ""
    lines = [x.strip() for x in text.splitlines() if x.strip()]
    first = lines[0] if lines else ""

    # Keep name exactly, remove only leading country flag.
    first = re.sub(r"^\s*🇯🇵\s*", "", first)
    parts = first.split("|", 1)
    name = parts[0].strip() if parts else None
    rarity = parts[1].strip() if len(parts) > 1 else None

    mid = re.search(r"ID\s*:\s*(\d+)", text, re.I)

    return ParsedCharacter(
        name=name,
        id=int(mid.group(1)) if mid else None,
        rarity=rarity,
        raw=text,
    )
