# Operator on None must raise TypeError not Hole — catch-all `_ => Hole` is
# UNSOUND; must be `_ => exception(TypeError)` to catch bugs
"""
In CPython, applying an operator to None raises TypeError:
    None + 1  → TypeError
    None < 5  → TypeError
    None * 3  → TypeError

Under tag-based dispatch, `PAdd(from_None(), from_int(1))` has no
matching case. It falls to Hole — an unconstrained value.

But Hole is NOT TypeError. Hole means "could be anything" — the solver
treats it as an unknown value that might satisfy any assertion. This is
UNSOUND: the model says "might succeed" when CPython always crashes.

The correct behavior: operators on None must produce `exception(TypeError)`
(not Hole). This way the exception propagation mechanism (finding 173)
can catch it.

Uses ONLY confirmed-accepted constructs: Optional, int, try/except.
"""
from typing import Optional


def add_to_none() -> int:
    """None + 1 must raise TypeError."""
    try:
        x: Optional[int] = None
        result = x + 1  # type: ignore — TypeError in CPython
        return result
    except TypeError:
        return -1


def compare_none() -> int:
    """None < 5 must raise TypeError."""
    try:
        x: Optional[int] = None
        if x < 5:  # type: ignore — TypeError in CPython
            return 1
        return 0
    except TypeError:
        return -1


def none_in_arithmetic_chain() -> int:
    """None flowing into arithmetic must not silently produce garbage."""
    try:
        x: Optional[int] = None
        y: int = x * 2 + 1  # type: ignore
        return y
    except TypeError:
        return -1


def guarded_operation(x: Optional[int]) -> int:
    """Correct pattern: check for None before operating."""
    if x is None:
        return 0
    return x + 1  # safe: x is narrowed to int


def main() -> None:
    # Operations on None raise TypeError
    assert add_to_none() == -1
    assert compare_none() == -1
    assert none_in_arithmetic_chain() == -1

    # Guarded operation works
    assert guarded_operation(5) == 6
    assert guarded_operation(None) == 0

    print(add_to_none(), compare_none(), guarded_operation(5))


main()
