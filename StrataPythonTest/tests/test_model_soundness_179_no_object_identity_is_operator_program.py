# `is None` / `is not None` correctly modeled as tag check — general `is` must
# remain OUT (no object identity in model)
"""
The model has "No object identity." The `is` operator checks identity
(same object in memory), not equality. The subset says `is None` and
`is not None` are IN, but `x is y` for non-None is OUT.

However, the model must still correctly handle the SEMANTICS of `is None`:
- `x is None` must be True only when x is actually None
- `x is not None` must be True when x is any non-None value
- These must work for Optional[T] variables

The deeper issue: under value semantics, two objects with identical fields
are INDISTINGUISHABLE. There's no way to tell if they're "the same object"
or "two objects with the same values." This is fine for `is None` (None is
a singleton) but would break `is` on other types if it were IN.

This finding verifies that `is None` / `is not None` work correctly and
documents why general `is` must remain OUT.

Uses ONLY confirmed-accepted constructs: is None, is not None, Optional.
"""
from typing import Optional


def check_is_none(x: Optional[int]) -> bool:
    return x is None


def check_is_not_none(x: Optional[int]) -> bool:
    return x is not None


def safe_unwrap(x: Optional[int], default: int) -> int:
    if x is not None:
        return x
    return default


def none_propagation(a: Optional[int], b: Optional[int]) -> Optional[int]:
    """Return sum if both present, else None."""
    if a is None:
        return None
    if b is None:
        return None
    return a + b


def chain_none_checks(x: Optional[int]) -> str:
    if x is None:
        return "none"
    if x > 0:
        return "positive"
    if x < 0:
        return "negative"
    return "zero"


def identity_not_equality() -> bool:
    """
    In CPython: two distinct objects with same fields are `==` but not `is`.
    Under value semantics: they're indistinguishable (no identity).
    This is why `is` on non-None must be OUT.
    """
    # For None, `is` and `==` are the same (singleton)
    a: Optional[int] = None
    b: Optional[int] = None
    assert a is None
    assert b is None
    # a is b would be True in CPython (same None singleton)
    # Under value semantics, also True (both are from_None())
    return True


def main() -> None:
    # is None
    assert check_is_none(None) == True
    assert check_is_none(5) == False
    assert check_is_none(0) == False  # 0 is not None!

    # is not None
    assert check_is_not_none(None) == False
    assert check_is_not_none(5) == True
    assert check_is_not_none(0) == True

    # Safe unwrap
    assert safe_unwrap(42, 0) == 42
    assert safe_unwrap(None, 0) == 0

    # None propagation
    assert none_propagation(3, 4) == 7
    assert none_propagation(None, 4) is None
    assert none_propagation(3, None) is None

    # Chain
    assert chain_none_checks(None) == "none"
    assert chain_none_checks(5) == "positive"
    assert chain_none_checks(-3) == "negative"
    assert chain_none_checks(0) == "zero"

    # Identity
    assert identity_not_equality() == True

    print(check_is_none(None), safe_unwrap(None, -1),
          chain_none_checks(5))


main()
