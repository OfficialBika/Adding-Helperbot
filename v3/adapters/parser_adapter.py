class ParserAdapter:
    """Convert existing parser output into V3 pipeline input."""

    def adapt(self, parsed_data):
        if isinstance(parsed_data, dict):
            return parsed_data

        return {
            "raw": parsed_data,
        }
