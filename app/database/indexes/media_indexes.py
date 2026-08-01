MEDIA_INDEXES = [
    {
        "keys": [("unique_id", 1)],
        "options": {"unique": True},
    },
    {
        "keys": [("created_at", -1)],
        "options": {},
    },
    {
        "keys": [("media_type", 1)],
        "options": {},
    },
]


async def create_media_indexes(collection):
    for index in MEDIA_INDEXES:
        await collection.create_index(
            index["keys"],
            **index["options"],
        )
