from app.database.repositories.hash_repository import hash_repository


class ImageStorageService:
    async def save_image(self, file_id: str, hash_value: str):
        existing = await hash_repository.find_by_hash(hash_value)
        if existing:
            return {"duplicate": True, "record": existing}

        await hash_repository.save({
            "file_id": file_id,
            "hash_value": hash_value,
        })

        return {"duplicate": False}


image_storage_service = ImageStorageService()
