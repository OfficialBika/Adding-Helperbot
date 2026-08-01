from aiogram import Router
from aiogram.filters import Command
from aiogram.types import Message

from app.admin.checks import admin_checker

router = Router()


@router.message(Command("status"))
async def status(message: Message):
    if not admin_checker.is_admin(message.from_user.id):
        return

    await message.answer("Adding HelperBot V3 status: OK")
