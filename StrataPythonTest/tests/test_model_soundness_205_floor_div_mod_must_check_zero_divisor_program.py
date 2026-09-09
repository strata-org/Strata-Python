# Floor div / mod must check zero divisor — SMT div-by-zero is undefined not
# error; must explicitly produce exception(ZeroDivisionError)
"""
`//` and `%` must check for zero divisor and produce ZeroDivisionError.
Under tag-based dispatch, the operator function receives the operands
and must:
1. Check if divisor is zero
2. If zero: return exception(ZeroDivisionError)
3. If non-zero: compute the result

Finding 080 identified that float division by zero doesn't raise
(SMT Real division is total). This finding covers `//` and `%` on
INTEGERS where division by zero must raise.

If the model computes `PFloorDiv(from_int(10), from_int(0))` without
checking, SMT integer division by zero is undefined (solver picks
arbitrary value). The model must explicitly produce an exception.

Uses ONLY confirmed-accepted constructs: int, //, %, try/except.
"""


def floor_div_by_zero() -> int:
    """10 // 0 must raise ZeroDivisionError."""
    try:
        result: int = 10 // 0
        return result
    except ZeroDivisionError:
        return -1


def mod_by_zero() -> int:
    """10 % 0 must raise ZeroDivisionError."""
    try:
        result: int = 10 % 0
        return result
    except ZeroDivisionError:
        return -1


def true_div_by_zero() -> int:
    """10 / 0 must raise ZeroDivisionError."""
    try:
        result: float = 10 / 0
        return 0
    except ZeroDivisionError:
        return -1


def guarded_division(a: int, b: int) -> int:
    """Correct pattern: check before dividing."""
    if b == 0:
        return 0
    return a // b


def division_in_loop(xs: list[int], divisor: int) -> list[int]:
    """Divide all elements — must handle zero divisor."""
    if divisor == 0:
        return []
    result: list[int] = []
    for x in xs:
        result.append(x // divisor)
    return result


def mod_for_even_check(n: int) -> bool:
    """n % 2 — divisor is literal 2, never zero."""
    return n % 2 == 0


def main() -> None:
    # Division by zero raises
    assert floor_div_by_zero() == -1
    assert mod_by_zero() == -1
    assert true_div_by_zero() == -1

    # Guarded division
    assert guarded_division(10, 3) == 3
    assert guarded_division(10, 0) == 0

    # Division in loop
    assert division_in_loop([10, 20, 30], 5) == [2, 4, 6]
    assert division_in_loop([10, 20], 0) == []

    # Mod with non-zero literal
    assert mod_for_even_check(4) == True
    assert mod_for_even_check(7) == False

    print(floor_div_by_zero(), guarded_division(10, 3),
          mod_for_even_check(4))


main()
