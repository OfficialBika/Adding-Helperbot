class SourceMapper:
    """Maps source bots to their lookup collections."""

    def __init__(self):
        self.mapping = {
            "character_catcher": "character_lookup",
            "grab": "grab_lookup",
            "senpai": "senpai_lookup",
            "hallow": "hallow_lookup",
            "takers": "takers_lookup",
        }

    def get_collection(self, source_bot: str):
        return self.mapping.get(source_bot)

    def register(self, source_bot: str, collection: str):
        self.mapping[source_bot] = collection


source_mapper = SourceMapper()
