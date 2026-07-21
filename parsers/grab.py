"""Grab Garden (/grab) parser."""
import re
from .base import ParsedCharacter

def parse(text: str) -> ParsedCharacter:
    text = text or ""
    lines = [x.strip() for x in text.splitlines() if x.strip()]

    # Grab Garden format:
    # Anime title
    # 1456: Ai Hoshino 👘
    # (🃏 CATEGORY: Divine)
    name = lines[1] if len(lines) > 1 else None
    mid = re.search(r"(?m)^\s*(\d+)\s*:\s*(.+?)\s*$", text)
    category = re.search(r"CATEGORY\s*:\s*(.+)", text, re.I)

    # Existing project behavior expects anime/source title as name.
    source_name = lines[1-1] if lines else name

    return ParsedCharacter(
        name=source_name.strip() if source_name else name,
        id=int(mid.group(1)) if mid else None,
        rarity=("🃏 " + category.group(1).strip()) if category else None,
        raw=text,
    )
