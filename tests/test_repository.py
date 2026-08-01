import pytest

from app.database.repositories.hash_repository import HashRepository
from app.database.repositories.user_repository import UserRepository


@pytest.mark.asyncio
async def test_hash_repository_without_database():
    repo = HashRepository()

    result = await repo.find_by_hash("test_hash")

    assert result is None


@pytest.mark.asyncio
async def test_user_repository_without_database():
    repo = UserRepository()

    result = await repo.save({"user_id": 1})

    assert result is None
