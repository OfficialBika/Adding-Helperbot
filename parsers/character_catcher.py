"""Character Catcher (/catch) parser."""
import re
from .base import ParsedCharacter

def parse(text: str) -> ParsedCharacter:
    text = text or ""
    mid = re.search(r"(?m)^\s*(\d+)\s*:\s*(.+?)\s*$", text)
    rarity = re.search(r"RARITY\s*:\s*(.+)", text, re.I)
    name = mid.group(2).strip() if mid else None
    return ParsedCharacter(
        name=name,
        id=int(mid.group(1)) if mid else None,
        rarity=rarity.group(1).strip() if rarity else None,
        raw=text,
    )
