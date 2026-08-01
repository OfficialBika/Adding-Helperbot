class StatisticsService:
    def __init__(self):
        self.images_processed = 0
        self.users_registered = 0

    def add_image(self):
        self.images_processed += 1

    def add_user(self):
        self.users_registered += 1

    def get(self):
        return {
            "images": self.images_processed,
            "users": self.users_registered,
        }


statistics_service = StatisticsService()
