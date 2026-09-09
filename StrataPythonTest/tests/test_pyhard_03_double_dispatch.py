class Forward:
    def __add__(self, other):
        return NotImplemented


class Reflected(Forward):
    def __radd__(self, other) -> int:
        return 7


def custom(left: Forward, right: Reflected) -> int:
    return left + right


def correlated_builtin(flag: bool) -> int | str:
    if flag:
        left = 1
        right = 2
    else:
        left = "a"
        right = "b"
    return left + right
