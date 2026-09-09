class Left:
    def __lt__(self, other):
        return NotImplemented


class Right:
    def __gt__(self, other) -> bool:
        raise LookupError()


def compare() -> str:
    try:
        result = Left() < Right()
        return "missed-exception"
    except LookupError:
        return "caught-reflected-error"


result = compare()
