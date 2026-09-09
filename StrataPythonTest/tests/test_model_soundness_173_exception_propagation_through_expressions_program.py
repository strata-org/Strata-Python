# Exception propagation through expressions — `exception(...)` tag must short-
# circuit all subsequent operations until caught
"""
The `exception(get_error: Error)` tag in `Any` represents an exception
value. When an operation produces an exception (e.g., division by zero),
the result is `exception(...)`.

But what happens when this exception value flows into the NEXT operation?

    x = 1 / 0          # exception(ZeroDivisionError)
    y = x + 1          # CPython: never reaches here (exception propagates)
                       # Model: PAdd(exception(...), from_int(1)) → ???

In CPython, exceptions propagate via the call stack — once raised, no
subsequent expression evaluates. In the model, exception is just a TAG
in the union. If operators don't check for it, the exception silently
disappears and garbage propagates.

Finding 079 identified this for operators. This finding shows the FULL
propagation chain: exceptions must poison ALL subsequent operations
until caught by try/except.

Uses ONLY confirmed-accepted constructs: try/except, int, division.
"""


def division_propagates(a: int, b: int) -> int:
    """If b is 0, the exception must propagate — x+1 never executes."""
    try:
        x: int = a // b  # raises if b == 0
        y: int = x + 1   # only executes if no exception
        return y
    except ZeroDivisionError:
        return -1


def chained_operations(a: int, b: int) -> int:
    """Multiple operations after a potential exception."""
    try:
        x: int = a // b      # might raise
        y: int = x * 2       # should not execute if x is exception
        z: int = y + 10      # should not execute if y is exception
        return z
    except ZeroDivisionError:
        return 0


def exception_in_condition(a: int, b: int) -> int:
    """Exception in a condition expression."""
    try:
        ratio: int = a // b
        if ratio > 5:  # if ratio is exception, this comparison is undefined
            return 1
        return 0
    except ZeroDivisionError:
        return -1


def exception_as_function_arg(a: int, b: int) -> int:
    """Exception value passed as argument to another function."""
    try:
        x: int = a // b
        y: int = abs(x)  # abs of exception value?
        return y
    except ZeroDivisionError:
        return -1


def main() -> None:
    # Normal case — no exception
    assert division_propagates(10, 2) == 6  # 10//2=5, 5+1=6
    # Exception case — division by zero caught
    assert division_propagates(10, 0) == -1

    # Chained
    assert chained_operations(10, 2) == 20  # 5*2=10, 10+10=20
    assert chained_operations(10, 0) == 0

    # In condition
    assert exception_in_condition(20, 3) == 1  # 20//3=6, 6>5 → 1
    assert exception_in_condition(10, 3) == 0  # 10//3=3, 3>5 → 0
    assert exception_in_condition(10, 0) == -1

    # As function arg
    assert exception_as_function_arg(-10, 2) == 5  # -10//2=-5, abs(-5)=5
    assert exception_as_function_arg(10, 0) == -1

    print(division_propagates(10, 2), chained_operations(10, 0),
          exception_in_condition(10, 0))


main()
