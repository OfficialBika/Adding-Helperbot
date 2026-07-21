"""Takers (/take) parser."""
import re
from .base import ParsedCharacter

def parse(text):
    n=re.search(r"Name:\s*(.+)",text)
    r=re.search(r"Rarity:\s*(.+)",text)
    i=re.search(r"Character ID:\s*(\d+)",text)
    return ParsedCharacter(n.group(1).strip() if n else None,int(i.group(1)) if i else None,r.group(1).strip() if r else None,text)
