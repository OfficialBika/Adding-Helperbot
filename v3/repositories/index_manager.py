class IndexManager:
    """Define MongoDB indexes required for fast lookup queries."""

    DEFAULT_INDEXES = [
        {"field": "file_unique_id", "unique": True},
        {"field": "name", "unique": False},
        {"field": "source_bot", "unique": False},
        {"field": "created_at", "unique": False},
    ]

    def get_indexes(self):
        return self.DEFAULT_INDEXES

    async def create_indexes(self, collection):
        if collection is None:
            return None

        for index in self.DEFAULT_INDEXES:
            await collection.create_index(
                index["field"],
                unique=index["unique"],
            )


index_manager = IndexManager()
