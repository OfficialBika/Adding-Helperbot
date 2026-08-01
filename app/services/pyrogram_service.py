from pyrogram import Client

from app.config.settings import settings


class PyrogramService:
    def __init__(self):
        self.client = Client(
            "adding_helper_v3",
            api_id=int(getattr(settings, "API_ID", 0) or 0),
            api_hash=getattr(settings, "API_HASH", ""),
            bot_token=settings.BOT_TOKEN,
        )

    async def start(self):
        await self.client.start()

    async def stop(self):
        await self.client.stop()


pyrogram_service = PyrogramService()
