# Exception persists in variable — `x = raise(); y = x + 1` continues
# executing; exception infects all subsequent uses of x
"""
EXCEPTION PERSISTS IN VARIABLE — USED LATER WITHOUT CHECK

CPython: x = might_raise(-1)  → raises, x never assigned, code stops.
Model:   x = exception(ValueError(...))  → x holds exception value.
         Later: y = x + 1  → PAdd(exception(...), from_int(1)) → Hole
         Even later: return y  → returns Hole (passes type assertion!)

The exception is "trapped" in variable x. It doesn't propagate.
All subsequent uses of x produce Hole (or wrong values).
The program continues executing as if nothing happened.

This is the TEMPORAL aspect of the propagation problem:
the exception persists across multiple statements, infecting
every expression that touches the variable.
"""


def might_raise(x: int) -> int:
    if x < 0:
        raise ValueError("negative")
    return x


def exception_persists() -> int:
    """Exception trapped in variable, used multiple times."""
    x: int = might_raise(-1)
    # CPython: raises here, nothing below executes
    # Model: x = exception(ValueError), execution continues

    y: int = x + 10      # PAdd(exception, int) → Hole
    z: int = y * 2       # PMul(Hole, int) → Hole
    w: int = z - 1       # PSub(Hole, int) → Hole
    return w             # returns Hole — may pass int assertion!


def exception_in_condition() -> str:
    """Exception-valued variable used in if condition."""
    x: int = might_raise(-1)
    # CPython: raises, if never reached
    # Model: x = exception(...), flows into condition
    if x > 0:
        return "positive"
    else:
        return "non-positive"
    # Model: condition is Hole → non-deterministic branch


def exception_used_much_later() -> int:
    """Exception assigned early, used many statements later."""
    x: int = might_raise(-1)
    # CPython: raises immediately

    # Model: 10 statements of "normal" code execute
    a: int = 1
    b: int = 2
    c: int = a + b
    d: int = c * 2
    e: int = d + 1

    # Then x is used — exception surfaces here
    result: int = x + e
    return result


def main() -> None:
    # Test 1: exception persists
    raised: bool = False
    try:
        exception_persists()
    except ValueError:
        raised = True
    assert raised

    # Test 2: exception in condition
    raised2: bool = False
    try:
        exception_in_condition()
    except ValueError:
        raised2 = True
    assert raised2

    # Test 3: exception used later
    raised3: bool = False
    try:
        exception_used_much_later()
    except ValueError:
        raised3 = True
    assert raised3

    # Test 4: no exception path
    assert might_raise(5) == 5

    print("all passed")


main()
