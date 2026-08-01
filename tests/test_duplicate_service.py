import pytest

from app.services.duplicate_service import duplicate_service


@pytest.mark.asyncio
async def test_duplicate_detection():
    result = await duplicate_service.compare(
        "abc123",
        ["abc123", "xyz789"],
    )

    assert result is True


@pytest.mark.asyncio
async def test_new_image_detection():
    result = await duplicate_service.compare(
        "new_hash",
        ["abc123"],
    )

    assert result is False
