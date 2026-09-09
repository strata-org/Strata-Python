# `is None` narrowing for Optional types — tag-set narrowing after `is None`
# guard needed for safe unwrap of Optional[T]
"""
Python's `None` comparison uses `is` (identity), not `==` (equality).
`x is None` checks reference identity. In the model, `from_None()` is
a value constructor — `PEq(from_None(), from_None())` should return True,
and `PIs(x, from_None())` should check the tag.

The issue: if `is None` is translated as `PEq(x, from_None())`, it uses
structural equality which works. But if it's translated as a reference
identity check (which doesn't exist in the value model), it fails.

More subtly: `x is not None` as a narrowing guard must EXCLUDE the
from_None tag from x's tag set for subsequent code. If the model doesn't
narrow after `is None` checks, Optional[T] handling is broken.
"""
from typing import Optional


def safe_divide(a: int, b: int) -> Optional[int]:
    if b == 0:
        return None
    return a // b


def unwrap_or(value: Optional[int], default: int) -> int:
    if value is None:
        return default
    return value


def chain_optional(a: int, b: int, c: int) -> Optional[int]:
    r1: Optional[int] = safe_divide(a, b)
    if r1 is None:
        return None
    r2: Optional[int] = safe_divide(r1, c)
    return r2


def main() -> None:
    # safe_divide returns None on zero divisor
    assert safe_divide(10, 2) == 5
    assert safe_divide(10, 0) is None

    # unwrap_or: None check then use
    assert unwrap_or(42, 0) == 42
    assert unwrap_or(None, -1) == -1

    # chain: propagate None
    assert chain_optional(100, 5, 2) == 10
    assert chain_optional(100, 0, 2) is None
    assert chain_optional(100, 5, 0) is None

    print(safe_divide(10, 2), unwrap_or(None, -1), chain_optional(100, 5, 2))


main()
