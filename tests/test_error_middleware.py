import pytest

from app.middlewares.error import error_middleware


async def failing_handler(event, data):
    raise RuntimeError("test error")


@pytest.mark.asyncio
async def test_error_middleware_catches_exception():
    result = await error_middleware(
        failing_handler,
        None,
        {},
    )

    assert result is None
