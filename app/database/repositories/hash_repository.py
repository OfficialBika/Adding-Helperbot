class HashRepository:
    def __init__(self, database=None):
        self.database = database

    async def find_by_hash(self, hash_value: str):
        if self.database and self.database.db:
            return await self.database.db.images.find_one({"hash_value": hash_value})
        return None

    async def save(self, data: dict):
        if self.database and self.database.db:
            return await self.database.db.images.insert_one(data)
        return None


hash_repository = HashRepository()
