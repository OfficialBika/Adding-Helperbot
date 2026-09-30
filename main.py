"""Compatibility entrypoint for Render services still configured as 'python main.py'."""

import asyncio

from unified.main import run


if __name__ == "__main__":
    asyncio.run(run())
