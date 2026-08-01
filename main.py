import asyncio
import logging

from aiogram import Dispatcher

from app.bot.client import bot_client


logging.basicConfig(level=logging.INFO)


dp = Dispatcher()


async def main():
    bot = bot_client.get()
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())
