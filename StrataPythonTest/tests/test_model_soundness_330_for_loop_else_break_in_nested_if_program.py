# `for/else` with conditional break — else execution depends on runtime path;
# break-flag must be symbolic variable
"""
for/else with break inside nested if — break reachability determines else.

Finding 065 covers for/else basic semantics. Finding 316 covers while/else.
This finding tests a subtler case: break is inside a CONDITIONAL in the
loop body. The else block's execution depends on whether the break was
ACTUALLY TAKEN (runtime path), not just whether it EXISTS (static).

    for x in xs:
        if condition(x):
            break
    else:
        # Runs if break was NEVER taken across ALL iterations
        # i.e., condition(x) was False for every x

The model must track that:
1. If the loop completes all iterations without break → else runs
2. If break fires on ANY iteration → else is skipped
3. The break is conditional — it may or may not fire depending on data

This is harder than unconditional break because the model can't
statically determine whether else runs — it depends on the loop's
runtime behavior.

Uses ONLY confirmed-accepted constructs: for, if, break, else, list, int.
"""


def find_or_default(xs: list[int], target: int) -> int:
    """for/else search pattern — else means 'not found'."""
    result: int = -1
    for x in xs:
        if x == target:
            result = x
            break
    else:
        # Only reached if target not in xs (no break taken)
        result = 0
    return result
    # CPython with xs=[1,2,3], target=2: break fires → result=2
    # CPython with xs=[1,2,3], target=9: no break → else runs → result=0
    # Model: if else always runs: target=2 → result=0 WRONG
    # Model: if else never runs: target=9 → result=-1 WRONG


def all_positive(xs: list[int]) -> bool:
    """Check if all elements are positive using for/else."""
    for x in xs:
        if x <= 0:
            break
    else:
        # No non-positive element found
        return True
    return False
    # CPython with [1,2,3]: True (else runs)
    # CPython with [1,-1,3]: False (break at -1)


def find_first_divisor(n: int) -> int:
    """Find smallest divisor > 1, or return 0 if prime."""
    for d in range(2, n):
        if n % d == 0:
            break
    else:
        # No divisor found — n is prime
        return 0
    return d  # type: ignore  # d is the divisor that caused break


def conditional_break_accumulator(xs: list[int], limit: int) -> int:
    """Accumulate until limit exceeded; else adds bonus."""
    total: int = 0
    for x in xs:
        total = total + x
        if total > limit:
            break
    else:
        # Completed without exceeding limit
        total = total + 1000
    return total
    # CPython with xs=[1,2,3], limit=100: no break → 6+1000=1006
    # CPython with xs=[1,2,3], limit=4: break at x=3 (total=6>4) → 6


def main() -> None:
    assert find_or_default([1, 2, 3], 2) == 2
    assert find_or_default([1, 2, 3], 9) == 0
    assert all_positive([1, 2, 3]) == True
    assert all_positive([1, -1, 3]) == False
    assert all_positive([]) == True  # empty → else runs
    assert find_first_divisor(7) == 0  # prime
    assert find_first_divisor(12) == 2
    assert conditional_break_accumulator([1, 2, 3], 100) == 1006
    assert conditional_break_accumulator([1, 2, 3], 4) == 6
