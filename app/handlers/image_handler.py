from aiogram import Router
from aiogram.types import Message

from app.services.image_service import image_service
from app.services.hash_service import hash_service
from app.services.media_service import media_service
from app.services.statistics_service import statistics_service
from app.services.image_storage_service import image_storage_service

router = Router()


@router.message()
async def process_image(message: Message):
    if not message.photo:
        return

    photo = message.photo[-1]
    data = await media_service.download_photo(
        message.bot,
        photo.file_id,
    )

    valid = await image_service.validate(data)
    if not valid:
        await message.answer("Invalid image")
        return

    image_hash = await hash_service.calculate(data)
    result = await image_storage_service.save_image(
        photo.file_id,
        image_hash,
    )

    statistics_service.add_image()

    if result.get("duplicate"):
        await message.answer("Duplicate image detected")
        return

    await message.answer(
        f"Image saved successfully\nHash: {image_hash}"
    )
