from dataclasses import dataclass

@dataclass(frozen=True)
class SourceConfig:
    key: str
    bot: str
    command: str

SOURCES = {
    "catch": SourceConfig("catch", "@Character_Catcher_Bot", "/check"),
    "grab": SourceConfig("grab", "@GrabGardenBot", "/check"),
    "senpai": SourceConfig("senpai", "@SenpaiBot", "/see"),
    "hallow": SourceConfig("hallow", "@Characters_Hallow_bot", "/show"),
    "takers": SourceConfig("takers", "@Takers_character_bot", "/detect"),
}
