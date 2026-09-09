# Exception value in condition position — if propagation checks missing,
# exception flows into if/while condition; causes non-deterministic branching
"""
What happens when an exception value appears in a CONDITION position?

    if exception_value:  # what does this mean?
    while exception_value:  # infinite loop? no loop?

In CPython, this never happens — exceptions unwind the stack before
reaching any condition. But under exception-as-value semantics, if
propagation checks are missing, an exception value CAN flow into a
condition.

The model must handle this: `Any_to_bool(exception(...))` must either:
1. Propagate the exception (correct)
2. Return Hole (dangerous — branch is non-deterministic)
3. Return True/False (wrong — exception is not a boolean)

Uses ONLY confirmed-accepted constructs: try/except, if, while, int.
"""


def exception_in_if_condition() -> int:
    """If exception reaches condition, it must propagate, not branch."""
    try:
        x: int = 1 // 0  # exception
        # In CPython: never reaches the if
        if x > 0:
            return 1
        return 0
    except ZeroDivisionError:
        return -1


def exception_in_while_condition() -> int:
    """Exception in while condition must not cause infinite loop."""
    try:
        divisor: int = 0
        x: int = 10 // divisor  # exception
        # In CPython: never reaches the while
        count: int = 0
        while x > 0:
            x = x - 1
            count = count + 1
        return count
    except ZeroDivisionError:
        return -1


def exception_in_and_chain() -> int:
    """Exception in boolean chain must propagate."""
    try:
        a: int = 1 // 0  # exception
        # In CPython: never evaluates the `and`
        if a > 0 and a < 100:
            return 1
        return 0
    except ZeroDivisionError:
        return -1


def safe_pattern() -> int:
    """Correct: check BEFORE potentially-raising operation."""
    divisor: int = 0
    if divisor != 0:
        return 10 // divisor
    return -1


def main() -> None:
    assert exception_in_if_condition() == -1
    assert exception_in_while_condition() == -1
    assert exception_in_and_chain() == -1
    assert safe_pattern() == -1

    print(exception_in_if_condition(), exception_in_while_condition(),
          safe_pattern())


main()
