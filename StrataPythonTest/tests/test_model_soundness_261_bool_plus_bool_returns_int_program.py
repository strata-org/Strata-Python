# `True + True` = 2 (int) — PAdd has no bool×bool case; CPython promotes to
# int arithmetic; model returns Hole
"""
CPython results (concrete):
  True + True  = 2  (type: int)
  True + False = 1  (type: int)
  False + False = 0 (type: int)
  True * 5     = 5  (type: int)

Laurel model results:
  PAdd(from_bool(True), from_bool(True))  = Hole (no bool×bool case)
  PAdd(from_bool(True), from_bool(False)) = Hole
  PMul(from_bool(True), from_int(5))      = Hole (no bool×int case)
"""


def bool_plus_bool(a: bool, b: bool) -> int:
    return a + b


def bool_times_int(a: bool, b: int) -> int:
    return a * b


def count_trues(flags: list[bool]) -> int:
    total: int = 0
    for f in flags:
        total = total + f  # bool + int
    return total


def main() -> None:
    # CPython: True + True = 2 (int)
    assert bool_plus_bool(True, True) == 2
    assert bool_plus_bool(True, False) == 1
    assert bool_plus_bool(False, False) == 0

    # CPython: True * 5 = 5 (int)
    assert bool_times_int(True, 5) == 5
    assert bool_times_int(False, 5) == 0

    # CPython: sum of bools = count of Trues
    assert count_trues([True, False, True, True]) == 3

    print(bool_plus_bool(True, True), bool_times_int(True, 5),
          count_trues([True, False, True]))


main()
