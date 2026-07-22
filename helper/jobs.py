import asyncio

class JobManager:
    def __init__(self):
        self.jobs = {}
        self.tasks = {}

    def create(self, source, start_id):
        self.jobs[source] = {"current_id": int(start_id), "status":"running"}

    def stop(self, source):
        if source in self.jobs:
            self.jobs[source]["status"]="paused"

    def get(self, source):
        return self.jobs.get(source)
