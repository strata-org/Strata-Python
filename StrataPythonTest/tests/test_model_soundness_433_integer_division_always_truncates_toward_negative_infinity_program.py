# `-7 // 2` → `-4` (floor toward -∞); model gives `-3` (SMT truncates toward
# 0); WRONG VALUE not Hole
"""
INTEGER FLOOR DIVISION TRUNCATES TOWARD NEGATIVE INFINITY

CPython: -7 // 2 → -4 (floor toward -∞)
         7 // -2 → -4 (floor toward -∞)
         -1 // 2 → -1 (floor toward -∞)

Model:   PFloorDiv uses SMT-LIB `div` which truncates toward ZERO:
         -7 div 2 → -3 (truncate toward 0) — WRONG!
         7 div -2 → -3 (truncate toward 0) — WRONG!
         -1 div 2 → 0 (truncate toward 0) — WRONG!

CPython result: -4
Model result: -3 (SPECIFIC WRONG VALUE — not Hole!)

Root cause: SMT-LIB integer division truncates toward zero.
Python floor division truncates toward negative infinity.
These DIFFER for negative operands. Finding 012/258/266/273/291.
"""


def floor_div_negative_dividend() -> list[int]:
    """Negative dividend — floor vs truncate diverges."""
    return [
        -7 // 2,   # CPython: -4, SMT: -3
        -1 // 2,   # CPython: -1, SMT: 0
        -10 // 3,  # CPython: -4, SMT: -3
        -5 // 2,   # CPython: -3, SMT: -2
    ]


def floor_div_negative_divisor() -> list[int]:
    """Negative divisor — also diverges."""
    return [
        7 // -2,   # CPython: -4, SMT: -3
        1 // -2,   # CPython: -1, SMT: 0
        10 // -3,  # CPython: -4, SMT: -3
    ]


def python_divmod(a: int, b: int) -> list[int]:
    """Python's invariant: a == (a // b) * b + (a % b)."""
    q: int = a // b
    r: int = a % b
    return [q, r]


def is_even(n: int) -> bool:
    """Common use of //: check parity via n // 2 * 2 == n."""
    return n == (n // 2) * 2


def main() -> None:
    # Test 1: negative dividend
    results: list[int] = floor_div_negative_dividend()
    assert results == [-4, -1, -4, -3]

    # Test 2: negative divisor
    results2: list[int] = floor_div_negative_divisor()
    assert results2 == [-4, -1, -4]

    # Test 3: divmod invariant
    # a == q * b + r must hold for ALL a, b
    dm: list[int] = python_divmod(-7, 2)
    assert dm[0] == -4 and dm[1] == 1  # -7 == -4*2 + 1 ✓
    assert dm[0] * 2 + dm[1] == -7

    dm2: list[int] = python_divmod(7, -2)
    assert dm2[0] == -4 and dm2[1] == -1  # 7 == -4*(-2) + (-1) = 8-1 = 7 ✓

    # Test 4: positive operands (both agree)
    assert 7 // 2 == 3
    assert 10 // 3 == 3

    # Test 5: is_even
    assert is_even(4)
    assert not is_even(5)
    assert is_even(-2)

    print("all passed")


main()
