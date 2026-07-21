from dataclasses import dataclass

@dataclass
class ParsedCharacter:
    name: str|None = None
    id: int|None = None
    rarity: str|None = None
    raw: str = ""
