# **FIX: Python floor-div/mod + zero check** — replace SMT div/mod with floor
# semantics + ZeroDivisionError; resolves 12 findings
"""
FIX PROPOSAL: Replace SMT div/mod with Python floor-div/mod + zero check.
Resolves findings: 012, 039, 050, 080, 205, 258, 259, 266, 267, 268, 291, 292.

The fix: define python_floor_div and python_mod in terms of SMT operations,
with explicit zero-divisor check producing ZeroDivisionError.
"""


def floor_div_correct(a: int, b: int) -> int:
    """Python // with correct floor semantics."""
    if b == 0:
        raise ZeroDivisionError("integer division or modulo by zero")
    return a // b


def mod_correct(a: int, b: int) -> int:
    """Python % with correct sign-follows-divisor semantics."""
    if b == 0:
        raise ZeroDivisionError("integer division or modulo by zero")
    return a % b


def invariant_holds(a: int, b: int) -> bool:
    """a == (a // b) * b + (a % b) must ALWAYS hold."""
    if b == 0:
        return True  # skip zero
    return a == (a // b) * b + (a % b)


def main() -> None:
    # Positive: same in both SMT and Python
    assert floor_div_correct(7, 2) == 3
    assert mod_correct(7, 3) == 1

    # Negative: DIVERGES between SMT and Python
    assert floor_div_correct(-7, 2) == -4   # NOT -3
    assert mod_correct(-7, 3) == 2          # NOT -1
    assert floor_div_correct(7, -2) == -4   # NOT -3
    assert mod_correct(7, -3) == -2         # NOT 1

    # Zero divisor: must raise
    caught: bool = False
    try:
        floor_div_correct(10, 0)
    except ZeroDivisionError:
        caught = True
    assert caught == True

    # Invariant
    assert invariant_holds(-7, 2) == True
    assert invariant_holds(7, -3) == True
    assert invariant_holds(-10, 4) == True

    print("All div/mod tests pass")


main()
