from io import BytesIO

from PIL import Image
import imagehash


class HashService:
    async def calculate(self, data: bytes):
        image = Image.open(BytesIO(data))
        return str(imagehash.phash(image))


hash_service = HashService()
