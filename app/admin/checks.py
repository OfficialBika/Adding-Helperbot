from app.config.settings import settings


class AdminChecker:
    def is_admin(self, user_id: int) -> bool:
        admins = getattr(settings, "ADMIN_IDS", "")
        if not admins:
            return False
        return user_id in [int(x) for x in admins.split(",") if x]


admin_checker = AdminChecker()
