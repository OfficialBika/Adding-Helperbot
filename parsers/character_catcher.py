"""Character Catcher (/catch) parser."""
import re
from .base import ParsedCharacter

def parse(text):
    m_id=re.search(r"(\d+)\s*:", text)
    m_name=re.search(r"\d+\s*:\s*(.+)", text)
    m_r=re.search(r"RARITY:\s*(.+)", text)
    return ParsedCharacter(m_name.group(1).strip() if m_name else None,int(m_id.group(1)) if m_id else None,m_r.group(1).strip() if m_r else None,text)
