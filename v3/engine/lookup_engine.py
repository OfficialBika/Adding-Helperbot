from v3.adapters.adapter_manager import adapter_manager


class LookupEngine:
    """Main coordinator for parser adapters and lookup pipeline."""

    def __init__(self, pipeline=None):
        self.pipeline = pipeline

    async def process(self, source_bot: str, parsed_data: dict):
        adapter = adapter_manager.get_adapter(source_bot)

        if adapter is None:
            return {
                "status": "unsupported_source",
                "source_bot": source_bot,
            }

        adapted_data = adapter.adapt(parsed_data)

        if self.pipeline:
            return await self.pipeline.process(
                adapted_data,
                source_bot,
            )

        return {
            "status": "ready",
            "data": adapted_data,
        }


lookup_engine = LookupEngine()
