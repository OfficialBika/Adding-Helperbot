
import asyncio

class DMManager:
    def __init__(self):
        self.tasks = {}

    def add(self, key, task):
        self.stop(key)
        self.tasks[key] = task

    def stop(self, key):
        task = self.tasks.pop(key, None)
        if task and not task.done():
            task.cancel()

    async def stop_all(self):
        tasks=list(self.tasks.values())
        self.tasks.clear()
        for task in tasks:
            if task and not task.done():
                task.cancel()
        if tasks:
            await asyncio.gather(*tasks, return_exceptions=True)

    def running(self, key=None):
        if key:
            return key in self.tasks and not self.tasks[key].done()
        return bool(self.tasks)
