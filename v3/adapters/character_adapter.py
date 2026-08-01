from v3.adapters.parser_adapter import ParserAdapter


class CharacterAdapter(ParserAdapter):
    """Adapter for character based parsers."""

    def adapt(self, parsed_data):
        data = super().adapt(parsed_data)

        return {
            "name": data.get("name", ""),
            "file_id": data.get("file_id", ""),
            "file_unique_id": data.get("file_unique_id", ""),
            "media_type": data.get("media_type", "unknown"),
            "raw": data,
        }


character_adapter = CharacterAdapter()
