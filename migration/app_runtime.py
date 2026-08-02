"""Helpers used while migrating app.py to the new architecture.

Keeps startup/shutdown wiring separate from bot handlers.
"""

from database import startup_database, shutdown_database


async def initialize_runtime():
    await startup_database()


async def close_runtime():
    await shutdown_database()
