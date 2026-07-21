"""Hallow (/hallow) parser."""
import re
from .base import ParsedCharacter

def parse(text: str) -> ParsedCharacter:
    text = text or ""
    n = re.search(r"Character\s*Name\s*:\s*(.+)", text, re.I)
    r = re.search(r"Rarity\s*:\s*(.+)", text, re.I)
    i = re.search(r"ID\s*:\s*(\d+)", text, re.I)
    return ParsedCharacter(
        name=n.group(1).strip() if n else None,
        id=int(i.group(1)) if i else None,
        rarity=r.group(1).strip() if r else None,
        raw=text,
    )
