# `is None` must translate to tag check (`isfrom_None`), not `PEq` — avoids
# cross-tag Hole from finding 076
"""
`x is None` and `x == None` have different semantics in CPython:
- `is` checks object IDENTITY (same memory address)
- `==` checks VALUE equality (calls __eq__)

For None specifically, they're equivalent (None is a singleton). But
the model has no object identity — `is` must be translated differently
from `==`. The subset says `is` is only for None, so `is None` should
translate to a tag check (`isfrom_None`), not to PEq.
"""
from typing import Optional


def check_is_none(x: Optional[int]) -> bool:
    return x is None


def check_eq_none(x: Optional[int]) -> bool:
    return x == None  # type: ignore


def check_is_not_none(x: Optional[int]) -> bool:
    return x is not None


def safe_unwrap(x: Optional[int], default: int) -> int:
    if x is None:
        return default
    return x


def chain_none_checks(a: Optional[int], b: Optional[int]) -> int:
    if a is not None:
        return a
    if b is not None:
        return b
    return 0


def main() -> None:
    # is None
    assert check_is_none(None) == True
    assert check_is_none(5) == False
    assert check_is_none(0) == False  # 0 is not None!

    # == None (same result for None singleton)
    assert check_eq_none(None) == True
    assert check_eq_none(5) == False

    # is not None
    assert check_is_not_none(None) == False
    assert check_is_not_none(5) == True

    # Safe unwrap
    assert safe_unwrap(None, -1) == -1
    assert safe_unwrap(42, -1) == 42

    # Chain
    assert chain_none_checks(None, None) == 0
    assert chain_none_checks(None, 5) == 5
    assert chain_none_checks(3, 5) == 3

    print(check_is_none(None), check_is_none(0), safe_unwrap(None, -1))


main()
