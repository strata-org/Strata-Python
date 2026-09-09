# Interaction: user raises matched through the real hierarchy: a user
# subclass is caught by its ancestor; SystemExit raised deliberately is
# NOT caught by except Exception and escapes to the module footer.
class AppError(Exception):
    pass


class ConfigError(AppError):
    pass


def load(flag: bool) -> int:
    try:
        if flag:
            raise ConfigError()
        return 1
    except AppError:
        return 2


def bail(code: int) -> int:
    try:
        if code > 0:
            raise SystemExit()
        return 0
    except Exception:
        return -1


r1 = load(True)
r2 = bail(1)
