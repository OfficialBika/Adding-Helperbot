"""Grab Garden (/grab) parser."""
import re
from .base import ParsedCharacter

def parse(text):
    i=re.search(r"(\d+)\s*:",text)
    r=re.search(r"CATEGORY:\s*(.+)",text)
    name=text.splitlines()[1].strip() if len(text.splitlines())>1 else None
    return ParsedCharacter(name,int(i.group(1)) if i else None,r.group(1).strip() if r else None,text)
