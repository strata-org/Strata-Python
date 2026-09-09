class ContainsBomb:
    def __contains__(self, item) -> bool:
        raise LookupError()


def contains() -> str:
    try:
        result = 1 in ContainsBomb()
        return "missed-exception"
    except LookupError:
        return "caught-contains-error"


result = contains()
