# `try/except/else` clause — `else` runs only when no exception raised in try;
# model has no conditional path for this block
"""
TRY/EXCEPT/ELSE clause — the `else` block runs ONLY when no exception
was raised in the `try` block. The model has no representation for this
conditional execution path.

    try:
        result = int(s)
    except ValueError:
        result = -1
    else:
        result = result * 2  # only runs if int(s) succeeded

CPython semantics:
- `else` executes if and only if the `try` block completed without raising
- `else` does NOT execute if an exception was raised (even if caught)
- `else` runs BEFORE `finally`

The Laurel encoding models exceptions as values (finding 274). Even if
exception propagation is fixed (finding 298), the `else` clause requires
knowing WHETHER an exception occurred — a boolean condition on the
exception path that the current encoding doesn't track.

Uses ONLY confirmed-accepted constructs: try, except, else, int, str, function.
"""


def parse_or_double(s: str) -> int:
    """Parse string to int; if successful, double it; if not, return -1."""
    result: int = 0
    try:
        result = int(s)
    except ValueError:
        result = -1
    else:
        # This ONLY runs if int(s) did NOT raise
        result = result * 2
    return result


def safe_divide_with_logging(a: int, b: int) -> int:
    """Divide a by b; else clause confirms success."""
    result: int = 0
    succeeded: bool = False
    try:
        if b == 0:
            raise ValueError("division by zero")
        result = a // b
    except ValueError:
        result = -1
    else:
        # Only runs if no exception — division succeeded
        succeeded = True
    # CPython: succeeded is True only when b != 0
    # Model: may always or never execute else block
    if succeeded:
        return result
    return -1


def else_not_on_caught(xs: list[int], idx: int) -> int:
    """Else does NOT run even if exception is caught."""
    value: int = 0
    ran_else: bool = False
    try:
        if idx < 0 or idx >= len(xs):
            raise IndexError("out of bounds")
        value = xs[idx]
    except IndexError:
        value = -999
    else:
        # Only runs if NO exception was raised
        ran_else = True
        value = value + 1

    # CPython: if idx is invalid, ran_else is False, value is -999
    # CPython: if idx is valid, ran_else is True, value is xs[idx] + 1
    # Model without else semantics: may execute else unconditionally
    #   → value = -999 + 1 = -998 (WRONG for invalid idx)
    #   OR may skip else entirely
    #   → value = xs[idx] without +1 (WRONG for valid idx)
    return value


def else_with_finally(n: int) -> int:
    """Else runs before finally; both interact with return values."""
    result: int = 0
    try:
        if n < 0:
            raise ValueError("negative")
        result = n
    except ValueError:
        result = 0
    else:
        result = result + 100  # add bonus for success
    # CPython: n >= 0 → result = n + 100
    # CPython: n < 0 → result = 0 (else skipped)
    return result


def main() -> None:
    # parse_or_double: successful parse gets doubled
    assert parse_or_double("5") == 10   # int("5")=5, else: 5*2=10
    assert parse_or_double("abc") == -1  # ValueError, else skipped

    # safe_divide_with_logging
    assert safe_divide_with_logging(10, 2) == 5   # success, else runs
    assert safe_divide_with_logging(10, 0) == -1  # exception, else skipped

    # else_not_on_caught
    xs: list[int] = [10, 20, 30]
    assert else_not_on_caught(xs, 1) == 21   # valid: 20 + 1
    assert else_not_on_caught(xs, 5) == -999  # invalid: exception caught

    # else_with_finally
    assert else_with_finally(7) == 107   # success: 7 + 100
    assert else_with_finally(-3) == 0    # exception: else skipped

    print("All try/except/else tests pass")


main()
