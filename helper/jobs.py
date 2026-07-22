from datetime import datetime

class JobManager:
    def __init__(self):
        self.jobs = {}
        self.tasks = {}

    def create(self, source, start_id):
        self.jobs[source] = {
            "source": source,
            "current_id": int(start_id),
            "status": "running",
            "retry": 0,
            "updated_at": datetime.utcnow().isoformat(),
        }
        return self.jobs[source]

    def update_id(self, source, value):
        if source in self.jobs:
            self.jobs[source]["current_id"] = int(value)

    def stop(self, source):
        if source in self.jobs:
            self.jobs[source]["status"] = "paused"

    def get(self, source):
        return self.jobs.get(source)
