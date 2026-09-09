# Optional[T] requires disjunctive tag assertion — `assert(isfrom_int(x) \|\|
# isfrom_None(x))` needed for narrowing after `is not None`
"""
`Optional[int]` means the value can be `int` or `None`. The model must
track a TAG SET for such variables: {from_int, from_None}.

After `if x is not None`, the tag set narrows to {from_int}.
Before the check, operations on x must account for BOTH possibilities.

The key issue: how does the model represent "x is Optional[int]"?
- Option 1: `assert(isfrom_int(x) || isfrom_None(x))` — disjunction
- Option 2: no assertion (x is unconstrained Any) — too weak
- Option 3: separate tracking per branch — SSA-style

If the model uses Option 2 (no assertion), then x could be from_str
or from_float — the Optional constraint is lost entirely.

Uses ONLY confirmed-accepted constructs: Optional, is None, int, str.
"""
from typing import Optional


def unwrap_or_default(x: Optional[int], default: int) -> int:
    if x is None:
        return default
    return x  # narrowed to int


def optional_chain(a: Optional[int], b: Optional[int]) -> Optional[int]:
    """Both must be non-None to add."""
    if a is None:
        return None
    if b is None:
        return None
    return a + b


def optional_field_access(name: Optional[str]) -> int:
    """Use Optional[str] — must narrow before calling len."""
    if name is None:
        return 0
    return len(name)


def multiple_optionals(x: Optional[int], y: Optional[int], z: Optional[int]) -> int:
    """Sum of non-None values."""
    total: int = 0
    if x is not None:
        total = total + x
    if y is not None:
        total = total + y
    if z is not None:
        total = total + z
    return total


def optional_in_loop(xs: list[Optional[int]]) -> int:
    """Sum non-None elements."""
    total: int = 0
    for x in xs:
        if x is not None:
            total = total + x
    return total


def main() -> None:
    assert unwrap_or_default(5, 0) == 5
    assert unwrap_or_default(None, 0) == 0

    assert optional_chain(3, 4) == 7
    assert optional_chain(None, 4) is None
    assert optional_chain(3, None) is None

    assert optional_field_access("hello") == 5
    assert optional_field_access(None) == 0

    assert multiple_optionals(1, None, 3) == 4
    assert multiple_optionals(None, None, None) == 0

    assert optional_in_loop([1, None, 3, None, 5]) == 9

    print(unwrap_or_default(5, 0), optional_chain(3, 4),
          optional_in_loop([1, None, 3]))


main()
