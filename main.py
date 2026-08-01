import asyncio

from aiogram import Dispatcher

from app.bot.client import bot_client
from app.database.connection import database
from app.handlers.loader import register_handlers
from app.middlewares.error import error_middleware
from app.middlewares.user import user_middleware
from app.services.database_service import database_service
from app.services.pyrogram_service import pyrogram_service
from app.utils.logger import logger


async def main():
    dp = Dispatcher()

    dp.message.middleware(error_middleware)
    dp.message.middleware(user_middleware)

    register_handlers(dp)

    await database.connect()
    await database_service.initialize_indexes()
    await pyrogram_service.start()

    logger.info("Database, indexes and Pyrogram initialized")

    try:
        logger.info("Adding HelperBot V3 started")
        await dp.start_polling(bot_client.get())
    finally:
        await pyrogram_service.stop()
        await database.close()
        await bot_client.get().session.close()
        logger.info("Shutdown completed")


if __name__ == "__main__":
    asyncio.run(main())
