# List multiplication `[0] * n` — PMul has no (from_ListAny, from_int) case;
# list repetition returns Hole
"""
LIST MULTIPLICATION: `[0] * n` creates a list of n copies.

The subset allows `list * int` (analogous to `str * int`), but the model
has no `PMul(from_ListAny, from_int)` case. Finding 285 covers `int * list`
(reflected dispatch), but this is the LEFT-primary case: list.__mul__(int).

CPython: [0] * 3 → [0, 0, 0], len([0]*3) == 3
Model:   PMul(from_ListAny(...), from_int(3)) → Hole (no case)

This is extremely common for initializing fixed-size arrays:
    visited: list[bool] = [False] * n
    matrix: list[int] = [0] * size

Root cause: PMul operator dispatch has no (ListAny, int) case.
Related: finding 015 (str*int negative), 262 (str*int), 285 (int*list).
This is the MISSING SYMMETRIC CASE for lists.
"""


def zeros(n: int) -> list[int]:
    """Create a list of n zeros."""
    return [0] * n


def repeat_element(x: int, n: int) -> list[int]:
    """Create a list repeating x, n times."""
    return [x] * n


def init_flags(size: int) -> list[bool]:
    """Common pattern: initialize boolean array."""
    return [False] * size


def repeat_then_modify(n: int) -> list[int]:
    """Create repeated list, then modify one element."""
    result: list[int] = [0] * n
    if n > 0:
        result[0] = 1
    return result


def length_after_multiply(n: int) -> int:
    """len([x] * n) must equal max(0, n)."""
    xs: list[int] = [1] * n
    return len(xs)


def main() -> None:
    # Basic list multiplication
    assert zeros(3) == [0, 0, 0]
    assert zeros(0) == []
    assert zeros(1) == [0]

    # Repeat element
    assert repeat_element(7, 4) == [7, 7, 7, 7]
    assert repeat_element(5, 0) == []

    # Boolean flags initialization
    flags: list[bool] = init_flags(3)
    assert flags == [False, False, False]
    assert len(flags) == 3

    # Modify after creation
    assert repeat_then_modify(3) == [1, 0, 0]
    assert repeat_then_modify(0) == []

    # Length axiom
    assert length_after_multiply(5) == 5
    assert length_after_multiply(0) == 0

    # Negative multiplier gives empty list
    assert [1, 2] * (-1) == []

    print(zeros(3), repeat_element(7, 2), length_after_multiply(4))


main()
