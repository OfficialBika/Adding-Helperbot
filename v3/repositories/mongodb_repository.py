from dataclasses import asdict


class MongoDBLookupRepository:
    """Database access layer for lookup bot records.

    Keeps MongoDB operations separate from parsers and commands.
    """

    def __init__(self, collection=None):
        self.collection = collection

    async def insert(self, record):
        if self.collection is None:
            return None

        return await self.collection.insert_one(asdict(record))

    async def find_by_file_unique_id(self, file_unique_id: str):
        if self.collection is None:
            return None

        return await self.collection.find_one(
            {"file_unique_id": file_unique_id}
        )

    async def update(self, file_unique_id: str, data: dict):
        if self.collection is None:
            return None

        return await self.collection.update_one(
            {"file_unique_id": file_unique_id},
            {"$set": data},
        )


mongodb_lookup_repository = MongoDBLookupRepository()
