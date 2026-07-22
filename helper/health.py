from datetime import datetime, timezone

def helper_status(jobs):
    return {
        "jobs": jobs,
        "checked_at": datetime.now(timezone.utc).isoformat()
    }
