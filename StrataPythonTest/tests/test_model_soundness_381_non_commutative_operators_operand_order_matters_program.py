# Non-commutative operators (-, /, //, %, **) — operand order matters; swapped
# operands produce WRONG VALUE not Hole
"""
NON-COMMUTATIVE OPERATORS — OPERAND ORDER MATTERS IN TAG DISPATCH

CPython: 10 - 3 = 7, but 3 - 10 = -7. Order matters.
         10 / 3 = 3.33, but 3 / 10 = 0.3. Order matters.
         10 // 3 = 3, but 3 // 10 = 0. Order matters.
         10 % 3 = 1, but 3 % 10 = 3. Order matters.
         2 ** 3 = 8, but 3 ** 2 = 9. Order matters.

Model:   PSub(from_int(a), from_int(b)) must compute a - b, NOT b - a.
         If the translator swaps operands when calling the operator
         function, or if the pattern match extracts them in wrong order,
         the result is WRONG (not Hole — a specific incorrect value).

For CROSS-TYPE operators, order is even more critical:
         10 - 1.5 = 8.5 (int - float → float)
         1.5 - 10 = -8.5 (float - int → float)
         The model must preserve which operand is left vs right.
"""


def subtraction_order(a: int, b: int) -> int:
    return a - b


def division_order(a: int, b: int) -> float:
    return a / b


def floor_div_order(a: int, b: int) -> int:
    return a // b


def mod_order(a: int, b: int) -> int:
    return a % b


def power_order(a: int, b: int) -> int:
    return a ** b


def cross_type_sub(a: int, b: float) -> float:
    """int - float: order determines sign."""
    return a - b


def main() -> None:
    # Test 1: subtraction is not commutative
    assert subtraction_order(10, 3) == 7
    assert subtraction_order(3, 10) == -7
    # If model swaps: both would give same result → WRONG

    # Test 2: division is not commutative
    assert abs(division_order(10, 4) - 2.5) < 0.001
    assert abs(division_order(4, 10) - 0.4) < 0.001

    # Test 3: floor div is not commutative
    assert floor_div_order(10, 3) == 3
    assert floor_div_order(3, 10) == 0

    # Test 4: modulo is not commutative
    assert mod_order(10, 3) == 1
    assert mod_order(3, 10) == 3

    # Test 5: power is not commutative
    assert power_order(2, 3) == 8
    assert power_order(3, 2) == 9

    # Test 6: cross-type subtraction order
    assert abs(cross_type_sub(10, 1.5) - 8.5) < 0.001
    assert abs(cross_type_sub(1, 10.5) - (-9.5)) < 0.001

    print("all passed")


main()
