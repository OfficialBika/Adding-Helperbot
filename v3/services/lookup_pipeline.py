from v3.normalizers.lookup_normalizer import lookup_normalizer


class LookupPipeline:
    """Build and store lookup records safely."""

    def __init__(self, repository=None, collection_manager=None, duplicate_checker=None):
        self.repository = repository
        self.collection_manager = collection_manager
        self.duplicate_checker = duplicate_checker

    async def process(self, parsed_data: dict, source_bot: str):
        collection = self.collection_manager.get_collection(source_bot)

        record = lookup_normalizer.normalize(
            parsed_data,
            source_bot=source_bot,
            collection=collection,
        )

        if self.duplicate_checker:
            if not await self.duplicate_checker.can_insert(record):
                return {"status": "duplicate", "record": record}

        if self.repository:
            result = await self.repository.insert(record)
            return {"status": "inserted", "result": result}

        return {"status": "ready", "record": record}


lookup_pipeline = LookupPipeline()
