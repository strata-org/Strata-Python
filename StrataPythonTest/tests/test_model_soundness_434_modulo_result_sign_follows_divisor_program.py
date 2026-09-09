# `-7 % 3` → `2` (sign follows divisor); model gives `-1` (SMT sign follows
# dividend); WRONG VALUE not Hole
"""
MODULO RESULT SIGN FOLLOWS DIVISOR (NOT DIVIDEND)

CPython: -7 % 3 → 2 (sign follows divisor: positive)
         7 % -3 → -2 (sign follows divisor: negative)
         -7 % -3 → -1 (sign follows divisor: negative)

Model:   PMod uses SMT-LIB `mod` where sign follows DIVIDEND:
         -7 mod 3 → -1 (sign follows dividend: negative) — WRONG!
         7 mod -3 → 1 (sign follows dividend: positive) — WRONG!

CPython result: 2
Model result: -1 (SPECIFIC WRONG VALUE)

Root cause: SMT-LIB mod semantics differ from Python %.
Python guarantees: 0 <= result < abs(divisor) when divisor > 0.
SMT guarantees: abs(result) < abs(divisor), sign matches dividend.
Finding 039/259/267/273/292.
"""


def mod_negative_dividend() -> list[int]:
    """Negative dividend, positive divisor."""
    return [
        -7 % 3,   # CPython: 2, SMT: -1
        -1 % 3,   # CPython: 2, SMT: -1
        -10 % 4,  # CPython: 2, SMT: -2
        -5 % 3,   # CPython: 1, SMT: -2
    ]


def mod_negative_divisor() -> list[int]:
    """Positive dividend, negative divisor."""
    return [
        7 % -3,   # CPython: -2, SMT: 1
        1 % -3,   # CPython: -2, SMT: 1
        10 % -4,  # CPython: -2, SMT: 2
    ]


def is_divisible(a: int, b: int) -> bool:
    """a % b == 0 means a is divisible by b."""
    return a % b == 0


def wrap_around(value: int, modulus: int) -> int:
    """Wrap value into [0, modulus) range — common use of %."""
    return value % modulus


def main() -> None:
    # Test 1: negative dividend
    results: list[int] = mod_negative_dividend()
    assert results == [2, 2, 2, 1]

    # Test 2: negative divisor
    results2: list[int] = mod_negative_divisor()
    assert results2 == [-2, -2, -2]

    # Test 3: Python invariant: a == (a // b) * b + (a % b)
    a: int = -7
    b: int = 3
    assert a == (a // b) * b + (a % b)  # -7 == -4*3 + 2 ✓ (-12 + 2 = nope, -4*3=-12+2=-10 nope)
    # Actually: -7 == (-3)*3 + 2 = -9+2 = -7? No: -7//3 = -3 in Python
    # Wait: -7//3 = -3 (floor). -3*3 = -9. -7 - (-9) = 2. So -7%3 = 2. ✓
    # Invariant: -7 == (-3)*3 + 2 → -7 == -9 + 2 → -7 == -7 ✓
    assert a // b == -3
    assert a % b == 2
    assert (a // b) * b + (a % b) == a

    # Test 4: wrap around (always non-negative for positive modulus)
    assert wrap_around(-1, 10) == 9
    assert wrap_around(15, 10) == 5
    assert wrap_around(0, 10) == 0

    # Test 5: divisibility
    assert is_divisible(10, 5)
    assert not is_divisible(10, 3)
    assert is_divisible(-6, 3)  # -6 % 3 == 0

    print("all passed")


main()
