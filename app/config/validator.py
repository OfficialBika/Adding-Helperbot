from app.config.settings import settings


class ConfigValidator:
    def validate(self):
        errors = []

        if not settings.BOT_TOKEN:
            errors.append("BOT_TOKEN is missing")

        return errors


config_validator = ConfigValidator()
