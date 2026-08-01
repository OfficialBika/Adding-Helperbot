class DuplicateChecker:
    """Prevent duplicate lookup records before database insert."""

    def __init__(self, repository=None):
        self.repository = repository

    async def exists(self, file_unique_id: str):
        if not self.repository:
            return False

        result = await self.repository.find_by_file_unique_id(file_unique_id)
        return result is not None

    async def can_insert(self, record):
        if not record.file_unique_id:
            return True

        return not await self.exists(record.file_unique_id)


duplicate_checker = DuplicateChecker()
