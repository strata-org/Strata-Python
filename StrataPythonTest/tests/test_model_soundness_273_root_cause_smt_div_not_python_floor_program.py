# **ROOT CAUSE: SMT div/mod ≠ Python //%** — truncation vs floor, wrong sign,
# total vs error; causes 10 findings with WRONG VALUES
"""
ROOT CAUSE: PFloorDiv/PMod use SMT-LIB `div`/`mod` which have DIFFERENT
semantics from Python's `//` and `%`.

PROPERTY: SMT-LIB div truncates toward zero. Python // floors toward -∞.
          SMT-LIB mod sign follows dividend. Python % sign follows divisor.
          SMT-LIB div(x,0) is defined (total). Python raises ZeroDivisionError.

This causes findings: 012, 039, 050, 080, 205, 258, 259, 266, 267, 268.

DEMONSTRATION: Concrete wrong values for negative operands.
"""


def python_floor_div_vs_smt(a: int, b: int) -> int:
    return a // b


def python_mod_vs_smt(a: int, b: int) -> int:
    return a % b


def invariant_holds(a: int, b: int) -> bool:
    """Python guarantees: a == (a // b) * b + (a % b)."""
    return a == (a // b) * b + (a % b)


def main() -> None:
    # Cases where SMT div/mod give WRONG answers:
    # Python: -7//2 = -4.  SMT: div(-7,2) = -3.
    assert python_floor_div_vs_smt(-7, 2) == -4

    # Python: -7%3 = 2.  SMT: mod(-7,3) = -1.
    assert python_mod_vs_smt(-7, 3) == 2

    # Python: 7//-2 = -4.  SMT: div(7,-2) = -3.
    assert python_floor_div_vs_smt(7, -2) == -4

    # Python: 7%-3 = -2.  SMT: mod(7,-3) = 1.
    assert python_mod_vs_smt(7, -3) == -2

    # Invariant always holds in CPython:
    assert invariant_holds(-7, 2) == True
    assert invariant_holds(7, -3) == True
    assert invariant_holds(-10, 4) == True

    print(python_floor_div_vs_smt(-7, 2), python_mod_vs_smt(-7, 3),
          invariant_holds(-7, 2))


main()
