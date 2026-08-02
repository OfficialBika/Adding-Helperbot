"""Basic import checks for the refactored database layer."""


def test_database_package_imports():
    from database import database, items_repo, users_repo

    assert database is not None
    assert items_repo is not None
    assert users_repo is not None
