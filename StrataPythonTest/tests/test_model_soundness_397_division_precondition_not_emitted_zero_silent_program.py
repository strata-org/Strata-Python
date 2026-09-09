# **PROMISE vs DELIVERY**: division precondition "emitted" but SMT div is
# total; `1//0` produces value not error — unsound
"""
DIVISION PRECONDITION NOT EMITTED — ZERO DIVISOR SILENT

The subset says: "Division preconditions: x / y, x // y, x % y require
y != 0. The verifier EMITS the precondition."

But finding 268 shows: `1 // 0` in the model produces "some int"
(SMT div is total), not an error. This means the precondition is
NOT actually emitted — or if emitted, it's not connected to the
division operation.

If the precondition IS emitted as `assert y != 0`:
  - Programs with provable non-zero divisor: verified ✓
  - Programs with possible zero divisor: "assertion may fail" ✓
  - Programs with definite zero divisor: "assertion fails" ✓

If the precondition is NOT emitted:
  - Division by zero silently produces a value (SMT div is total)
  - No error reported — UNSOUND
  - Programs that crash with ZeroDivisionError are "verified" ✓ (wrong!)
"""


def safe_division(a: int, b: int) -> int:
    """Caller guarantees b != 0 via precondition."""
    assert b != 0
    return a // b


def unsafe_division(a: int) -> int:
    """Division by zero — should be caught by verifier."""
    return a // 0  # ALWAYS crashes in CPython


def conditional_division(a: int, b: int) -> int:
    """Guard before division — precondition discharged by guard."""
    if b != 0:
        return a // b
    return 0


def division_in_loop(xs: list[int], divisor: int) -> list[int]:
    """Division in loop — precondition must hold for ALL iterations."""
    result: list[int] = []
    for x in xs:
        result.append(x // divisor)
    return result


def modulo_zero(a: int) -> int:
    """Modulo by zero — same precondition needed."""
    return a % 0  # ALWAYS crashes


def true_div_zero(a: int) -> float:
    """True division by zero."""
    return a / 0  # ALWAYS crashes (even for floats in Python)


def main() -> None:
    # Test 1: safe division works
    assert safe_division(10, 3) == 3

    # Test 2: unsafe division crashes
    raised: bool = False
    try:
        unsafe_division(5)
    except ZeroDivisionError:
        raised = True
    assert raised

    # Test 3: conditional division
    assert conditional_division(10, 2) == 5
    assert conditional_division(10, 0) == 0

    # Test 4: modulo zero crashes
    raised2: bool = False
    try:
        modulo_zero(5)
    except ZeroDivisionError:
        raised2 = True
    assert raised2

    # Test 5: true div zero crashes
    raised3: bool = False
    try:
        true_div_zero(5)
    except ZeroDivisionError:
        raised3 = True
    assert raised3

    print("all passed")


main()
