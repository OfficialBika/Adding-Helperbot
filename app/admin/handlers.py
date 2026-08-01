from aiogram import Router
from aiogram.filters import Command
from aiogram.types import Message

from app.admin.checks import admin_checker
from app.services.statistics_service import statistics_service
from app.services.health_service import health_service

router = Router()


@router.message(Command("status"))
async def status(message: Message):
    if not admin_checker.is_admin(message.from_user.id):
        return

    stats = statistics_service.get()
    health = await health_service.check()

    await message.answer(
        "Adding HelperBot V3 status: OK\n"
        f"Users: {stats['users']}\n"
        f"Images: {stats['images']}\n"
        f"Database: {health['database']}"
    )
