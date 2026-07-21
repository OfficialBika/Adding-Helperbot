"""Senpai (/pick) parser."""
import re
from .base import ParsedCharacter

def parse(text):
    lines=[x.strip() for x in text.splitlines() if x.strip()]
    first=lines[0] if lines else ""
    parts=first.split("|",1)
    name=parts[0].replace("🇯🇵","").strip()
    rarity=parts[1].strip() if len(parts)>1 else None
    mid=re.search(r"ID:\s*(\d+)",text)
    return ParsedCharacter(name,int(mid.group(1)) if mid else None,rarity,text)
