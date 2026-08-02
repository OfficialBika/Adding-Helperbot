from motor.motor_asyncio import AsyncIOMotorClient

from config import settings


class Database:
    def __init__(self):
        self.client = AsyncIOMotorClient(settings.mongo_uri)
        self.db = self.client[settings.db_name]

    def collection(self, name: str):
        return self.db[name]

    async def close(self):
        self.client.close()



database = Database()
