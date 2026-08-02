import os
from dataclasses import dataclass, field
from dotenv import load_dotenv

load_dotenv()


def parse_ids(value: str) -> set[int]:
    return {int(x.strip()) for x in (value or '').split(',') if x.strip().isdigit()}


def parse_chat_ref(value: str):
    value = (value or '').strip()
    return int(value) if value.lstrip('-').isdigit() else value


@dataclass(frozen=True)
class Settings:
    bot_token: str = field(default_factory=lambda: os.getenv('BOT_TOKEN', '').strip())
    mongo_uri: str = field(default_factory=lambda: os.getenv('MONGO_URI', '').strip())
    db_name: str = field(default_factory=lambda: os.getenv('DB_NAME', 'waifu_adding_v2').strip())
    owner_ids: set[int] = field(default_factory=lambda: parse_ids(os.getenv('OWNER_IDS', os.getenv('OWNER_ID', ''))))
    log_level: str = field(default_factory=lambda: os.getenv('LOG_LEVEL', 'INFO').upper())
    port: int = field(default_factory=lambda: int(os.getenv('PORT', '8080')))
    use_webhook: bool = field(default_factory=lambda: os.getenv('USE_WEBHOOK', 'false').lower() == 'true')

    def validate(self):
        if not self.bot_token:
            raise RuntimeError('BOT_TOKEN is required')
        if not self.mongo_uri:
            raise RuntimeError('MONGO_URI is required')
        if not self.owner_ids:
            raise RuntimeError('OWNER_ID or OWNER_IDS is required')


settings = Settings()
