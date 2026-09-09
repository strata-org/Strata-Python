# Bool arithmetic (`True + True`, `True * 5`) — `PAdd`/`PMul` don't normalize
# `from_bool` to `from_int`; result is Hole or wrong type
"""
Python's bool is a subclass of int. Arithmetic on booleans returns int,
not bool. PAdd(from_bool(true), from_bool(true)) in the Laurel encoding
likely returns from_bool (or Hole) rather than from_int(2).
"""


def count_flags(a: bool, b: bool, c: bool) -> int:
    # In Python: True + True + False == 2 (int)
    # bool.__add__ is inherited from int.__add__
    return a + b + c


def weighted_sum(flag: bool, value: int) -> int:
    # True * 5 == 5, False * 5 == 0
    return flag * value


def main() -> None:
    total: int = count_flags(True, True, False)
    # CPython: True + True + False = 1 + 1 + 0 = 2 (type: int)
    assert total == 2

    w: int = weighted_sum(True, 7)
    # CPython: True * 7 = 1 * 7 = 7 (type: int)
    assert w == 7

    # Direct arithmetic on bools
    x: int = True + 1
    # CPython: True + 1 = 2 (bool + int -> int)
    assert x == 2

    # Bool subtraction
    y: int = True - False
    # CPython: 1 - 0 = 1
    assert y == 1

    print(total, w, x, y)


main()
