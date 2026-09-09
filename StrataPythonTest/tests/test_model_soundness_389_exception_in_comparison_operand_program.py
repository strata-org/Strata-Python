# Exception in comparison operand — `if raise() > 0:` produces Hole condition;
# solver explores BOTH branches non-deterministically
"""
EXCEPTION IN COMPARISON OPERAND — NON-DETERMINISTIC BRANCHING

CPython: if might_raise(-1) > 0: → raises, neither branch taken.
Model:   if PGt(exception(...), from_int(0)): → Hole (unconstrained bool)
         Solver picks EITHER branch non-deterministically.
         Both branches are "reachable" — verification explores both.

This is UNSOUND in two ways:
1. Code in the TRUE branch executes with impossible preconditions
2. Code in the FALSE branch executes with impossible preconditions
3. The verifier may "prove" properties that depend on the branch choice

Finding 209 identified this issue. This finding provides the CONCRETE
program showing how non-deterministic branching leads to wrong proofs.
"""


def might_raise(x: int) -> int:
    if x < 0:
        raise ValueError("negative")
    return x


def exception_in_if_condition() -> str:
    """Exception in condition → neither branch should execute."""
    val: int = might_raise(-1)
    if val > 0:
        return "positive"
    else:
        return "non-positive"
    # CPython: raises at might_raise, never reaches if
    # Model: val = exception, val > 0 = Hole
    #   Solver explores BOTH branches → returns either string


def exception_in_while_condition() -> int:
    """Exception in while condition → loop should never execute."""
    limit: int = might_raise(-1)
    count: int = 0
    while count < limit:
        count += 1
    # CPython: raises at might_raise, while never reached
    # Model: limit = exception, count < exception = Hole
    #   Solver may enter loop 0 times or infinite times
    return count


def exception_guards_division() -> float:
    """Exception in guard → guarded code should be unreachable."""
    divisor: int = might_raise(-1)
    if divisor != 0:
        # This branch should be UNREACHABLE (exception before condition)
        # But model may enter it with divisor = exception
        return 100.0 / divisor  # division by exception → Hole
    return 0.0


def exception_in_assert() -> int:
    """Exception in assert condition."""
    x: int = might_raise(-1)
    assert x >= 0  # CPython: raises before assert
    # Model: assert Hole >= 0 → may pass or fail non-deterministically
    return x


def main() -> None:
    raised1: bool = False
    try:
        exception_in_if_condition()
    except ValueError:
        raised1 = True
    assert raised1

    raised2: bool = False
    try:
        exception_in_while_condition()
    except ValueError:
        raised2 = True
    assert raised2

    raised3: bool = False
    try:
        exception_guards_division()
    except ValueError:
        raised3 = True
    assert raised3

    raised4: bool = False
    try:
        exception_in_assert()
    except ValueError:
        raised4 = True
    assert raised4

    print("all passed")


main()
