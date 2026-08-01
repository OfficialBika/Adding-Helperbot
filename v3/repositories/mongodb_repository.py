from dataclasses import asdict


class MongoDBLookupRepository:
    """Database access layer for NameBotV3 lookup records."""

    def __init__(self, collection=None):
        self.collection = collection

    async def insert(self, record):
        if self.collection is None:
            return None

        return await self.collection.insert_one(asdict(record))

    async def find_by_file_unique_id(self, file_unique_id: str):
        if self.collection is None:
            return None

        return await self.collection.find_one({
            "file_unique_id": file_unique_id
        })

    async def find_by_fingerprint(self, fingerprint: str):
        if self.collection is None:
            return None

        return await self.collection.find_one({
            "$or": [
                {"sha256": fingerprint},
                {"phash": fingerprint},
            ]
        })

    async def upsert(self, record):
        """Insert or update lookup data without duplicating media."""

        if self.collection is None:
            return None

        document = asdict(record)

        return await self.collection.update_one(
            {"file_unique_id": record.file_unique_id},
            {
                "$set": document,
            },
            upsert=True,
        )

    async def update(self, file_unique_id: str, data: dict):
        if self.collection is None:
            return None

        return await self.collection.update_one(
            {"file_unique_id": file_unique_id},
            {"$set": data},
        )


mongodb_lookup_repository = MongoDBLookupRepository()
