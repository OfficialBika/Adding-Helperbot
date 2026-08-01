from io import BytesIO


class MediaService:
    async def download_photo(self, bot, file_id: str):
        buffer = BytesIO()
        await bot.download(file_id, destination=buffer)
        return buffer.getvalue()


media_service = MediaService()
