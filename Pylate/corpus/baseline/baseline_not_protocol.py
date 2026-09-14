class BoolBomb:
    def __bool__(self) -> bool:
        raise LookupError()


def negate() -> str:
    try:
        result = not BoolBomb()
        return "missed-exception"
    except LookupError:
        return "caught-bool-error"


result = negate()
