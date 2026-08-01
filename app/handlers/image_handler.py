from aiogram import Router
from aiogram.types import Message

from app.services.image_service import image_service

router = Router()


@router.message()
async def process_image(message: Message):
    if not message.photo:
        return

    await message.answer("Image received. Processing...")
