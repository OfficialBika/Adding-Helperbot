from motor.motor_asyncio import AsyncIOMotorClient

from app.config.settings import settings


class Database:
    def __init__(self):
        self.client = None
        self.db = None

    async def connect(self):
        if settings.DATABASE_URL:
            self.client = AsyncIOMotorClient(settings.DATABASE_URL)
            self.db = self.client.get_default_database()

    async def close(self):
        if self.client:
            self.client.close()


database = Database()
