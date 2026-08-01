from v3.normalizers.lookup_normalizer import lookup_normalizer


class LookupPipeline:
    """Connect parser output with V3 lookup storage flow."""

    def __init__(self, repository=None, collection_manager=None):
        self.repository = repository
        self.collection_manager = collection_manager

    async def process(self, parsed_data: dict, source_bot: str):
        collection = self.collection_manager.get_collection(source_bot)

        record = lookup_normalizer.normalize(
            parsed_data,
            source_bot=source_bot,
            collection=collection,
        )

        if self.repository:
            return await self.repository.insert(record)

        return record


lookup_pipeline = LookupPipeline()
