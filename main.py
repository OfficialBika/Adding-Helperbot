import asyncio

from aiogram import Dispatcher

from app.bot.client import bot_client
from app.database.connection import database
from app.handlers.loader import register_handlers
from app.utils.logger import logger


async def main():
    dp = Dispatcher()

    register_handlers(dp)

    await database.connect()
    logger.info("Database connected")

    try:
        logger.info("Adding HelperBot V3 started")
        await dp.start_polling(bot_client.get())
    finally:
        await database.close()
        await bot_client.get().session.close()
        logger.info("Shutdown completed")


if __name__ == "__main__":
    asyncio.run(main())
