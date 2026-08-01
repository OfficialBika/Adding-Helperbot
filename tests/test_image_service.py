import pytest

from app.services.image_service import image_service


@pytest.mark.asyncio
async def test_invalid_image_data():
    result = await image_service.validate(b"not-an-image")

    assert result is False
