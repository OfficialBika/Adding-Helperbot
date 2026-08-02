SOURCE_COLLECTIONS = {
    "character_catcher": "character_lookup",
    "grab": "grab_lookup",
    "senpai": "senpai_lookup",
    "hallow": "hallow_lookup",
    "takers": "takers_lookup",
}


def get_collection(source_bot: str):
    """Return MongoDB collection name for source bot."""

    return SOURCE_COLLECTIONS.get(
        source_bot,
        "default_lookup",
    )
