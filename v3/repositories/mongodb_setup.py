from v3.repositories.index_manager import index_manager
from v3.repositories.collection_initializer import collection_initializer


class MongoDBSetup:
    """Initialize MongoDB collections and indexes on startup."""

    def __init__(self, database=None):
        self.database = database

    async def setup(self, collections: list[str]):
        collection_list = await collection_initializer.ensure_sources(
            collections
        )

        for collection in collection_list:
            await index_manager.create_indexes(collection)

        return True


mongodb_setup = MongoDBSetup()
