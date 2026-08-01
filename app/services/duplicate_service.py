class DuplicateService:
    async def compare(self, current_hash: str, stored_hashes: list[str]):
        return current_hash in stored_hashes


duplicate_service = DuplicateService()
