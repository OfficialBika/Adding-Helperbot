from app.config.validator import config_validator


def test_config_validator():
    result = config_validator.validate()
    assert isinstance(result, list)
