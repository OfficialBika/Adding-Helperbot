import asyncio
import logging
from typing import Awaitable, Callable

logger = logging.getLogger(__name__)


class DMManager:
    """Manage long-running DM helper tasks safely.

    Prevents duplicated workers, handles cancellation cleanly,
    and keeps runtime state predictable after restart.
    """

    def __init__(self):
        self.tasks: dict[str, asyncio.Task] = {}

    def add(self, key: str, task: asyncio.Task):
        self.stop(key)
        self.tasks[key] = task

    def stop(self, key: str):
        task = self.tasks.pop(key, None)
        if task and not task.done():
            task.cancel()

    async def stop_all(self):
        tasks = list(self.tasks.values())
        self.tasks.clear()

        for task in tasks:
            if task and not task.done():
                task.cancel()

        if tasks:
            await asyncio.gather(*tasks, return_exceptions=True)

    def running(self, key: str | None = None) -> bool:
        if key:
            task = self.tasks.get(key)
            return bool(task and not task.done())

        return any(not task.done() for task in self.tasks.values())

    async def run_safe(self, key: str, worker: Callable[[], Awaitable]):
        """Run worker and automatically cleanup failed tasks."""
        async def wrapper():
            try:
                await worker()
            except asyncio.CancelledError:
                logger.info("DM worker cancelled: %s", key)
                raise
            except Exception:
                logger.exception("DM worker crashed: %s", key)
            finally:
                self.tasks.pop(key, None)

        task = asyncio.create_task(wrapper())
        self.add(key, task)
        return task
