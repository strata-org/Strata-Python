# `PMod` uses SMT-LIB Euclidean `%` — wrong sign when divisor is negative
# (Python `%` follows sign of divisor)
"""
PMod uses SMT-LIB '%' which is Euclidean modulo (result always >= 0 for
positive divisor, but wrong for negative divisor). Python's '%' follows
floor-division semantics: result has the sign of the divisor.

This is the PMod counterpart of finding 012 (PFloorDiv). Both use SMT-LIB
integer operations that diverge from Python on negative operands.
"""


def modulo_negative_divisor(a: int, b: int) -> int:
    # Python: 7 % (-3) = -2 (sign of divisor)
    # SMT-LIB: 7 mod (-3) = 7 mod 3 = 1 (Euclidean, always non-negative for pos divisor)
    # Actually SMT-LIB mod is: a - b * (a div b), where div is Euclidean
    # For negative b: result differs from Python
    return a % b


def modulo_negative_dividend(a: int, b: int) -> int:
    # Python: (-7) % 3 = 2 (sign of divisor, positive)
    # SMT-LIB Euclidean: (-7) mod 3 = 2 (same here, both non-negative)
    # But Python: (-7) % (-3) = -1 (sign of divisor, negative)
    # SMT-LIB: (-7) mod (-3) = (-7) mod 3 = 2 (Euclidean, always non-negative)
    return a % b


def main() -> None:
    # Case 1: positive dividend, negative divisor
    r1: int = modulo_negative_divisor(7, -3)
    print(r1)  # CPython: -2, Laurel/SMT: 1 (or 2 depending on SMT-LIB impl)

    # Case 2: negative dividend, negative divisor
    r2: int = modulo_negative_dividend(-7, -3)
    print(r2)  # CPython: -1, Laurel/SMT: 2

    # Case 3: verify the relationship a == (a // b) * b + (a % b)
    a: int = 7
    b: int = -3
    q: int = a // b   # CPython: -3 (floor). SMT: -2 (trunc)
    r: int = a % b    # CPython: -2. SMT: 1
    # CPython: (-3)*(-3) + (-2) = 9 - 2 = 7 ✓
    # SMT:     (-2)*(-3) + 1    = 6 + 1 = 7 ✓ (internally consistent but wrong values)
    print(q)  # CPython: -3
    print(r)  # CPython: -2


main()
