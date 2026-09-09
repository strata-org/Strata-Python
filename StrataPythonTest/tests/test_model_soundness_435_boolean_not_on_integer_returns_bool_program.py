# `not 0` → `True` (bool); PNot has no from_int case; must apply truthiness
# then negate; always returns from_bool
"""
`not` ON INTEGER RETURNS BOOL (NOT INTEGER)

CPython: not 0 → True (bool)
         not 5 → False (bool)
         not "" → True (bool)
         `not` ALWAYS returns a bool, regardless of operand type.

Model:   PNot(from_int(0)) → ???
         Finding 057/260 identified that PNot only handles from_bool.
         For from_int: either Hole (no case) or wrong type.

         Even if PNot handles from_int:
         - Must apply truthiness first: 0 is falsy, nonzero is truthy
         - Must return from_bool (not from_int)
         - `not 5` → from_bool(False), NOT from_int(0)

CPython result: not 0 → True (type: bool)
Model result: Hole (PNot has no from_int case)
"""


def not_zero() -> bool:
    """not 0 → True."""
    return not 0


def not_nonzero() -> bool:
    """not 5 → False."""
    return not 5


def not_empty_string() -> bool:
    """not "" → True."""
    return not ""


def not_nonempty_string() -> bool:
    """not "hello" → False."""
    return not "hello"


def negate_condition(x: int) -> bool:
    """Common pattern: not (x > 0) to check non-positive."""
    return not (x > 0)


def filter_falsy(xs: list[int]) -> list[int]:
    """Keep only truthy values using not."""
    result: list[int] = []
    for x in xs:
        if not not x:  # double-not to get truthiness as bool
            result.append(x)
    return result


def main() -> None:
    # Test 1: not on falsy int
    # CPython: True (bool)
    # Model: Hole (PNot has no from_int case)
    assert not_zero() == True

    # Test 2: not on truthy int
    assert not_nonzero() == False

    # Test 3: not on empty string
    assert not_empty_string() == True

    # Test 4: not on non-empty string
    assert not_nonempty_string() == False

    # Test 5: not on comparison result (this should work — comparison returns bool)
    assert negate_condition(5) == False
    assert negate_condition(-3) == True
    assert negate_condition(0) == True

    # Test 6: type is always bool
    result: bool = not 42
    assert result == False
    assert isinstance(result, bool)

    print("all passed")


main()
