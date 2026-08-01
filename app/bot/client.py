from aiogram import Bot

from app.config.settings import settings


class BotClient:
    def __init__(self):
        self.bot = Bot(token=settings.BOT_TOKEN)

    def get(self):
        return self.bot


bot_client = BotClient()
