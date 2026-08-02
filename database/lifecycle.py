import logging

from .client import database

logger = logging.getLogger(__name__)


async def startup_database():
    """Initialize database resources before bot startup."""
    try:
        await database.db.command('ping')
        logger.info('Database connection established')
    except Exception:
        logger.exception('Database connection failed')
        raise


async def shutdown_database():
    """Close database resources during application shutdown."""
    database.client.close()
    logger.info('Database connection closed')
