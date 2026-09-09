# Uncaught exception fails verification via return-type assertion —
# `exception(E)` doesn't match `isfrom_int`; this IS the soundness mechanism
# (positive)
"""
If a function can raise an exception and there's NO try/except handler,
the exception propagates to the caller. If the caller also has no handler,
it propagates further until it reaches the top level (program crash).

The verifier must DETECT this: a function that may produce an exception
value without catching it should be flagged as "may raise uncaught
exception" — this is a verification FAILURE (the program might crash).

Under exception-as-value semantics, an uncaught exception means the
function RETURNS an exception value instead of its declared return type.
The return-type assertion (`assert isfrom_int(result)`) would fire
because `exception(...)` is not `from_int(...)`.

This is how Frontend catches bugs: the type assertion fails, revealing
that the function might crash.

Uses ONLY confirmed-accepted constructs: function def, int, //.
"""


def always_safe(a: int, b: int) -> int:
    """Always safe: divisor is never zero."""
    if b == 0:
        return 0
    return a // b


def might_crash(a: int, b: int) -> int:
    """UNSAFE: no check before division. May raise ZeroDivisionError."""
    return a // b  # if b == 0, this crashes!


def caught_internally(a: int, b: int) -> int:
    """Safe: exception is caught internally."""
    try:
        return a // b
    except ZeroDivisionError:
        return 0


def propagates_to_caller() -> int:
    """Calls might_crash — exception propagates if b=0."""
    # If called with b=0, might_crash raises, this function also raises
    return might_crash(10, 2)  # safe with these specific args


def safe_caller() -> int:
    """Wraps unsafe function in try/except."""
    try:
        return might_crash(10, 0)
    except ZeroDivisionError:
        return -1


def main() -> None:
    # Always safe
    assert always_safe(10, 3) == 3
    assert always_safe(10, 0) == 0

    # Caught internally
    assert caught_internally(10, 2) == 5
    assert caught_internally(10, 0) == 0

    # Propagates (safe with non-zero arg)
    assert propagates_to_caller() == 5

    # Safe caller wraps unsafe
    assert safe_caller() == -1

    # might_crash with zero WOULD crash:
    crashed: bool = False
    try:
        might_crash(10, 0)
    except ZeroDivisionError:
        crashed = True
    assert crashed == True

    print(always_safe(10, 0), caught_internally(10, 0), safe_caller())


main()
