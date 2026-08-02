"""Basic checks for centralized configuration."""


def test_settings_object_exists():
    from config import settings

    assert settings is not None
    assert hasattr(settings, "bot_token")
    assert hasattr(settings, "mongo_uri")
    assert hasattr(settings, "db_name")
