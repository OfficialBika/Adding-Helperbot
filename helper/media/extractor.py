def extract_media(message):
    """Extract Telegram media information before saving to MongoDB."""

    data = {
        "media_type": "unknown",
        "file_id": "",
        "file_unique_id": "",
        "metadata": {},
    }

    if getattr(message, "photo", None):
        photo = message.photo[-1]

        data.update({
            "media_type": "photo",
            "file_id": photo.file_id,
            "file_unique_id": photo.file_unique_id,
            "metadata": {
                "width": photo.width,
                "height": photo.height,
            },
        })

    elif getattr(message, "video", None):
        video = message.video

        data.update({
            "media_type": "video",
            "file_id": video.file_id,
            "file_unique_id": video.file_unique_id,
            "metadata": {
                "width": video.width,
                "height": video.height,
                "duration": video.duration,
            },
        })

    return data


media_extractor = extract_media
