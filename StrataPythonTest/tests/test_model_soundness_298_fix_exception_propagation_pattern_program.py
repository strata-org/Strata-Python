# **FIX: Exception propagation pattern** — insert `if is_exception(x) { goto
# handler }` after raising ops; resolves 23+ findings
"""
FIX PROPOSAL: Exception propagation pattern for exception-as-value.
Resolves findings: 014, 025, 036, 052, 063, 079, 113-117, 160, 165,
173, 206-210, 249, 268-270.

The fix: after every potentially-raising operation, insert a check.
If exception, jump to handler. If no handler, propagate to caller.
"""


def demonstrates_correct_propagation() -> int:
    """With propagation checks, this works correctly."""
    try:
        a: int = 10
        b: int = 0
        c: int = a // b   # raises ZeroDivisionError
        d: int = c + 1    # SKIPPED (propagation check jumps to handler)
        return d           # SKIPPED
    except ZeroDivisionError:
        return -1          # REACHED correctly


def demonstrates_raise_terminates() -> int:
    """raise produces exception AND terminates."""
    try:
        raise ValueError("stop")
        return 999  # UNREACHABLE
    except ValueError:
        return 1


def demonstrates_type_matching() -> int:
    """Handler only catches matching type."""
    try:
        try:
            x: int = 1 // 0  # ZeroDivisionError
        except ValueError:   # WRONG type — doesn't catch
            return 1
        return 2             # UNREACHABLE (exception propagates)
    except ZeroDivisionError:
        return 3             # CORRECT handler


def demonstrates_per_iteration() -> list[int]:
    """try/except in loop: per-iteration handling."""
    results: list[int] = []
    divisors: list[int] = [2, 0, 3, 0, 5]
    for d in divisors:
        try:
            results.append(10 // d)
        except ZeroDivisionError:
            results.append(-1)
    return results


def main() -> None:
    assert demonstrates_correct_propagation() == -1
    assert demonstrates_raise_terminates() == 1
    assert demonstrates_type_matching() == 3
    assert demonstrates_per_iteration() == [5, -1, 3, -1, 2]

    print("All exception propagation tests pass")


main()
