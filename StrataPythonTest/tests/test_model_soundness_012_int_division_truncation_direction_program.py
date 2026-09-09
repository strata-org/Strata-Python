# PFloorDiv uses Euclidean division (SMT-LIB `div`); Python `//` is floor
# division — diverges on negative divisor
"""
Python's // is floor division (rounds toward -infinity).
The Laurel encoding uses SMT-LIB `div` which is Euclidean division
(remainder always non-negative). These differ when the divisor is negative.
"""

def divide_negative(a: int, b: int) -> int:
    # Python: 7 // (-2) = -4  (floor toward -inf)
    # SMT-LIB ediv: 7 div (-2) = -3  (remainder must be >= 0)
    return a // b

def modulo_negative(a: int, b: int) -> int:
    # Python: 7 % (-2) = -1  (sign follows divisor)
    # SMT-LIB emod: 7 mod (-2) = 1  (always non-negative)
    return a % b

def main() -> None:
    q: int = divide_negative(7, -2)
    r: int = modulo_negative(7, -2)
    # CPython: q == -4, r == -1, and 7 == (-2)*(-4) + (-1) ✓
    # Laurel:  q == -3, r == 1,  and 7 == (-2)*(-3) + 1    ✓ (Euclidean)
    # The invariant a == b*q + r holds in both, but q and r differ!
    print(q)  # CPython: -4, Laurel: -3
    print(r)  # CPython: -1, Laurel: 1

    # This assertion passes in CPython but FAILS in the Laurel model:
    assert q == -4  # CPython: True. Laurel: False (q is -3)

main()
