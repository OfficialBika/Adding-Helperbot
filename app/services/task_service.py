import asyncio


class TaskService:
    def __init__(self):
        self.tasks = set()

    def create(self, coroutine):
        task = asyncio.create_task(coroutine)
        self.tasks.add(task)
        task.add_done_callback(self.tasks.discard)
        return task


 task_service = TaskService()
".replace("

 task_service