import asyncio

class DMManager:
    def __init__(self):
        self.tasks = {}

    def add(self, key, task):
        old = self.tasks.get(key)
        if old:
            old.cancel()
        self.tasks[key] = task

    async def stop_all(self):
        for task in list(self.tasks.values()):
            if task:
                task.cancel()
        self.tasks.clear()

    def stop(self, key):
        task = self.tasks.pop(key, None)
        if task:
            task.cancel()
