# Return-type assertion must be at ALL exit points — early returns bypass end-
# of-function check; emit assert before each `assume(false)`
"""
Finding 131 says return-type assertions must be emitted. But they must
be emitted at EVERY return point, including:
- Explicit `return expr` statements
- Implicit `return None` at function end (for -> None functions)
- Returns inside try/except/finally
- Returns inside loops (early exit)

If the assertion is only at the LAST return, early returns bypass it.
If it's only at explicit returns, implicit None return bypasses it.

Uses ONLY confirmed-accepted constructs: function def, return, int, Optional.
"""
from typing import Optional


def multiple_returns(x: int) -> int:
    """Each return must be checked against -> int."""
    if x > 0:
        return x      # must assert isfrom_int
    if x < 0:
        return -x     # must assert isfrom_int
    return 0          # must assert isfrom_int


def early_return_in_loop(xs: list[int], target: int) -> int:
    """Return inside loop — must be type-checked."""
    for x in xs:
        if x == target:
            return x  # must assert isfrom_int
    return -1         # must assert isfrom_int


def return_in_try(s: str) -> int:
    """Returns in both try and except — both must be checked."""
    try:
        return int(s)     # must assert isfrom_int
    except ValueError:
        return -1         # must assert isfrom_int


def optional_return(x: int) -> Optional[int]:
    """Returns int or None — both must satisfy Optional[int] tag set."""
    if x >= 0:
        return x      # isfrom_int ✓ (subset of Optional[int])
    return None       # isfrom_None ✓ (subset of Optional[int])


def implicit_none_return(x: int) -> None:
    """Falling off end = implicit return None."""
    if x > 0:
        print(x)
    # implicit return None here — must produce from_None()


def main() -> None:
    assert multiple_returns(5) == 5
    assert multiple_returns(-3) == 3
    assert multiple_returns(0) == 0

    assert early_return_in_loop([1, 2, 3], 2) == 2
    assert early_return_in_loop([1, 2, 3], 9) == -1

    assert return_in_try("42") == 42
    assert return_in_try("bad") == -1

    assert optional_return(5) == 5
    assert optional_return(-1) is None

    implicit_none_return(5)  # should not crash

    print(multiple_returns(5), early_return_in_loop([1, 2, 3], 2),
          return_in_try("42"))


main()
