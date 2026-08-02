class CollectionInitializer:
    """Create and prepare lookup collections."""

    def __init__(self, database=None):
        self.database = database

    async def ensure_collection(self, collection_name: str):
        if self.database is None:
            return None

        existing = await self.database.list_collection_names()

        if collection_name not in existing:
            return await self.database.create_collection(collection_name)

        return self.database[collection_name]

    async def ensure_sources(self, collections: list[str]):
        result = []

        for collection in collections:
            result.append(
                await self.ensure_collection(collection)
            )

        return result


collection_initializer = CollectionInitializer()
