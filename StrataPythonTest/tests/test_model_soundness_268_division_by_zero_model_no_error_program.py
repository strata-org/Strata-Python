# `1 // 0`: CPython=ZeroDivisionError, Model=some int — SMT div is total;
# model misses the crash; unsound
"""
CPython: 1 // 0 → ZeroDivisionError (program crashes)
Model:   PFloorDiv(from_int(1), from_int(0)) = from_int(???) ← NO ERROR

SMT-LIB `div(1, 0)` is DEFINED (returns some arbitrary int).
The model says "this is fine, result is some int" when CPython CRASHES.

This is unsound: the model says "no error" when there IS an error.
"""


def divide_by_zero_floor() -> int:
    """CPython: raises ZeroDivisionError. Model: returns some int."""
    return 1 // 0


def divide_by_zero_mod() -> int:
    """CPython: raises ZeroDivisionError. Model: returns some int."""
    return 1 % 0


def divide_by_zero_true() -> float:
    """CPython: raises ZeroDivisionError. Model: returns some real."""
    return 1 / 0


def main() -> None:
    # All three MUST raise ZeroDivisionError
    caught1: bool = False
    try:
        divide_by_zero_floor()
    except ZeroDivisionError:
        caught1 = True
    assert caught1 == True

    caught2: bool = False
    try:
        divide_by_zero_mod()
    except ZeroDivisionError:
        caught2 = True
    assert caught2 == True

    caught3: bool = False
    try:
        divide_by_zero_true()
    except ZeroDivisionError:
        caught3 = True
    assert caught3 == True

    print(caught1, caught2, caught3)


main()
