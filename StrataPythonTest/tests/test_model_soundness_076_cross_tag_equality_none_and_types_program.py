# Cross-tag equality (`==`) — `None == 0` should be False, `1 == 1.0` should
# be True; `PEq` only handles same-tag
"""
Python's `==` across different types has specific rules:
- None == None → True
- None == <anything else> → False (never raises)
- int == float → numeric comparison (1 == 1.0 is True)
- bool == int → numeric (True == 1 is True)
- str == int → always False (no TypeError)

The model's PEq may only handle same-tag comparisons. Cross-tag PEq
(e.g., from_None vs from_int) may return Hole instead of False, or
may not handle the int/float numeric equivalence.
"""


def is_none(x: int) -> bool:
    # Comparing int to None: always False, never raises
    return x == None  # type: ignore


def none_equals_none() -> bool:
    a: None = None
    b: None = None
    return a == b


def int_equals_float(x: int, y: float) -> bool:
    return x == y


def not_equal_cross_type() -> bool:
    # These are all False — different types, no numeric equivalence
    a: str = "1"
    b: int = 1
    return a == b  # type: ignore


def find_none(xs: list[int]) -> int:
    """Contrived: check if element equals a sentinel."""
    count: int = 0
    for x in xs:
        if x == 0:
            count = count + 1
    return count


def main() -> None:
    # None == None is True
    assert none_equals_none() == True

    # int/float cross-type equality (numeric)
    assert int_equals_float(1, 1.0) == True
    assert int_equals_float(1, 1.5) == False
    assert int_equals_float(0, 0.0) == True

    # != across types
    assert (1 != 2.0) == True
    assert (1 != 1.0) == False

    # Cross-type == that's always False
    assert ("hello" == 5) == False  # type: ignore
    assert (None == 0) == False  # type: ignore
    assert (None == "") == False  # type: ignore
    assert (None == False) == False  # type: ignore

    # None != anything-non-None
    assert (None != 0) == True  # type: ignore
    assert (None != None) == False

    print(none_equals_none(), int_equals_float(1, 1.0), (None == 0))


main()
