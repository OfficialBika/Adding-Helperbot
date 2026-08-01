class CollectionManager:
    """Maps each bot/source to its lookup collection."""

    def __init__(self):
        self.collections = {}

    def register(self, source_bot: str, collection: str):
        self.collections[source_bot] = collection

    def get_collection(self, source_bot: str):
        return self.collections.get(source_bot)


collection_manager = CollectionManager()
