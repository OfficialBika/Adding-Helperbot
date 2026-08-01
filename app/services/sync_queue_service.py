from dataclasses import dataclass
from datetime import datetime


@dataclass
class SyncTask:
    payload: dict
    attempts: int = 0
    created_at: datetime = datetime.utcnow()


class SyncQueueService:
    """Lightweight queue for reliable lookup data synchronization."""

    def __init__(self):
        self.queue = []

    def add(self, payload: dict):
        self.queue.append(SyncTask(payload=payload))

    def next_task(self):
        if not self.queue:
            return None
        return self.queue.pop(0)

    def retry(self, task: SyncTask):
        task.attempts += 1
        self.queue.append(task)


sync_queue_service = SyncQueueService()
