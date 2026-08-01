from v3.adapters.parser_adapter import ParserAdapter


class SenpaiAdapter(ParserAdapter):
    """Adapter for senpai source parser output."""

    def adapt(self, parsed_data):
        data = super().adapt(parsed_data)

        return {
            "name": data.get("name", ""),
            "file_id": data.get("file_id", ""),
            "file_unique_id": data.get("file_unique_id", ""),
            "media_type": data.get("media_type", "unknown"),
            "tags": data.get("tags", []),
            "raw": data,
        }


senpai_adapter = SenpaiAdapter()
