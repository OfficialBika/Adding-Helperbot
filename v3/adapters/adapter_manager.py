from v3.adapters.character_adapter import character_adapter
from v3.adapters.grab_adapter import grab_adapter
from v3.adapters.senpai_adapter import senpai_adapter
from v3.adapters.hallow_adapter import hallow_adapter
from v3.adapters.takers_adapter import takers_adapter


class AdapterManager:
    """Select the correct adapter based on source bot."""

    def __init__(self):
        self.adapters = {
            "character_catcher": character_adapter,
            "grab": grab_adapter,
            "senpai": senpai_adapter,
            "hallow": hallow_adapter,
            "takers": takers_adapter,
        }

    def get_adapter(self, source_bot: str):
        return self.adapters.get(source_bot)

    def register(self, source_bot: str, adapter):
        self.adapters[source_bot] = adapter


adapter_manager = AdapterManager()
