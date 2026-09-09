# Type narrowing invalidated by reassignment — `assume(!isfrom_None(x))`
# becomes stale after `x = y`; UNSOUNDNESS if not killed
"""
After `isinstance` or `is not None` narrowing, the narrowed type
information must be INVALIDATED if the variable is reassigned.

Example:
    x: Optional[int] = get_value()
    if x is not None:
        # narrowed: x is int
        x = get_other_value()  # reassignment!
        # x is now Optional[int] again, NOT int
        print(x + 1)  # could crash if x is None

The Laurel model must track that reassignment invalidates narrowing.
If the `assume(isfrom_int(x))` persists after reassignment, the model
is unsound — it believes x is int when it might be None.

Uses ONLY confirmed-accepted constructs: Optional, if, is None, int.
"""
from typing import Optional


def safe_after_narrow(x: Optional[int]) -> int:
    if x is not None:
        # x is narrowed to int here
        return x + 1
    return 0


def reassign_breaks_narrow(x: Optional[int], y: Optional[int]) -> int:
    if x is not None:
        # x is narrowed to int
        val: int = x + 1
        x = y  # reassignment! x is now Optional[int] again
        # x might be None here — narrowing is gone
        if x is not None:
            return x + val
        return val
    return 0


def narrow_in_loop(xs: list[Optional[int]]) -> int:
    total: int = 0
    current: Optional[int] = None
    for item in xs:
        current = item  # each iteration reassigns
        if current is not None:
            total = total + current
    return total


def conditional_reassign(x: Optional[int], flag: bool) -> int:
    if x is not None:
        # x is int here
        if flag:
            x = None  # reassignment on one branch
        # After merge: x might be None (flag=True) or int (flag=False)
        # Narrowing from outer `if` is INVALID here
        if x is not None:
            return x
        return -1
    return 0


def main() -> None:
    # Basic narrowing works
    assert safe_after_narrow(5) == 6
    assert safe_after_narrow(None) == 0

    # Reassignment invalidates narrowing
    assert reassign_breaks_narrow(10, 20) == 31  # 10+1=11, x=20, 20+11=31
    assert reassign_breaks_narrow(10, None) == 11  # 10+1=11, x=None, return 11
    assert reassign_breaks_narrow(None, 5) == 0

    # Loop reassignment
    assert narrow_in_loop([1, None, 3, None, 5]) == 9  # 1+3+5

    # Conditional reassignment
    assert conditional_reassign(42, False) == 42
    assert conditional_reassign(42, True) == -1
    assert conditional_reassign(None, False) == 0

    print(reassign_breaks_narrow(10, 20), narrow_in_loop([1, None, 3]),
          conditional_reassign(42, True))


main()
