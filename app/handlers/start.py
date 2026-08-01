from aiogram import Router
from aiogram.filters import CommandStart
from aiogram.types import Message

from app.services.user_service import user_service

router = Router()


@router.message(CommandStart())
async def start_handler(message: Message):
    await user_service.register(message.from_user)
    await message.answer("Adding HelperBot V3 is running")
