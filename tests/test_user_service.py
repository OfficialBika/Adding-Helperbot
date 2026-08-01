import pytest

from app.services.user_service import user_service


class MockUser:
    id = 12345
    username = "tester"


@pytest.mark.asyncio
async def test_user_register():
    result = await user_service.register(MockUser())

    assert result is None
