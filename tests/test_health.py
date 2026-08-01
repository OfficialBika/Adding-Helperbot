import pytest

from app.services.health_service import health_service


@pytest.mark.asyncio
async def test_health_service():
    result = await health_service.check()

    assert "bot" in result
    assert "database" in result
