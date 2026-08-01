from io import BytesIO

from PIL import Image


class ImageService:
    async def validate(self, data: bytes) -> bool:
        try:
            Image.open(BytesIO(data)).verify()
            return True
        except Exception:
            return False


image_service = ImageService()
