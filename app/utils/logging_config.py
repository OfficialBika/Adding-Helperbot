import logging
import os


class LoggingConfig:
    def setup(self):
        level = os.getenv("LOG_LEVEL", "INFO").upper()

        logging.basicConfig(
            level=getattr(logging, level, logging.INFO),
            format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
        )


logging_config = LoggingConfig()
