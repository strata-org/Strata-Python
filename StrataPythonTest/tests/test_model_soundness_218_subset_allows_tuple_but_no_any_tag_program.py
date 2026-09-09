# Subset allows tuples but no Any tag exists — tuple[T1,T2] is IN but
# unrepresentable; encode as ClassInstance with _0,_1 fields
"""
The subset explicitly says:
  "tuple[T1, T2, ...] with explicit element types, fixed length" is IN.

But the Any datatype has no from_tuple constructor.
Finding 171 identified this. This finding provides the SUBSET-SPECIFIC
programs that are promised to work but can't be represented.

Key subset-promised tuple operations:
  - Literal construction: (1, "two")
  - Subscription: t[0], t[1]
  - Length: len(t)
  - Function return: def f() -> tuple[int, str]: return (1, "x")

Uses ONLY confirmed-accepted constructs: tuple, int, str, len.
"""
from typing import Tuple


def divmod_manual(a: int, b: int) -> Tuple[int, int]:
    """Return quotient and remainder — classic tuple return."""
    return (a // b, a % b)


def min_max(xs: list[int]) -> Tuple[int, int]:
    """Return (min, max) of a list."""
    lo: int = xs[0]
    hi: int = xs[0]
    for x in xs:
        if x < lo:
            lo = x
        if x > hi:
            hi = x
    return (lo, hi)


def unpack_and_use() -> int:
    """Use tuple elements after function return."""
    result: Tuple[int, int] = divmod_manual(17, 5)
    quotient: int = result[0]
    remainder: int = result[1]
    return quotient * 10 + remainder  # 3*10 + 2 = 32


def tuple_in_condition() -> bool:
    """Use tuple element in condition."""
    bounds: Tuple[int, int] = min_max([3, 1, 4, 1, 5])
    return bounds[0] == 1 and bounds[1] == 5


def tuple_length() -> int:
    t: Tuple[int, int, int] = (10, 20, 30)
    return len(t)  # 3


def main() -> None:
    assert divmod_manual(17, 5) == (3, 2)
    assert min_max([3, 1, 4, 1, 5]) == (1, 5)
    assert unpack_and_use() == 32
    assert tuple_in_condition() == True
    assert tuple_length() == 3

    print(divmod_manual(17, 5), unpack_and_use(), tuple_length())


main()
