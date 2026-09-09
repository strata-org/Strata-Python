# For-loop range variable final value off-by-one — CPython: `i == n-1` after
# `for i in range(n)`; model (while translation): `i == n`; empty range: model
# sets i=0, CPython preserves pre-loop value
"""
FOR-LOOP RANGE VARIABLE FINAL VALUE — OFF-BY-ONE AT LOOP EXIT

The subset allows:
  - for i in range(n) (IN)
  - Using loop variable after loop (IN — finding 156 confirms Python scoping)
  - Arithmetic on loop variable (IN)

The NOVEL gap: after `for i in range(n)` completes normally (no break),
the loop variable `i` holds the value `n-1` (the last value produced by
the iterator). But the model's while-loop translation may leave `i` at
a different value depending on where the increment happens.

Translation A (increment at end):
    i = 0; while i < n: BODY; i += 1
    → After loop: i == n (one past the last iteration)

Translation B (increment at start of next iteration):
    i = -1; while True: i += 1; if i >= n: break; BODY
    → After loop: i == n

CPython behavior:
    for i in range(5): pass
    → After loop: i == 4 (last value from iterator)

The model's while-loop translation leaves i == n (or n+1 depending on
translation), but CPython leaves i == n-1. This is an off-by-one error
that affects any code using the loop variable after the loop.

CRITICAL: This interacts with finding 156 (loop variable persists after
loop) — that finding establishes that the variable IS accessible, but
doesn't address what VALUE it has.

DISTINCT FROM:
  - Finding 156 (loop variable scope) — that's about accessibility;
    this is about the VALUE
  - Finding 414 (while loop counter final value) — that's about while
    loops; this is about for-range specifically
  - Finding 445 (range stop exclusive) — that's about iteration COUNT;
    this is about the FINAL VALUE of the variable after loop exit
  - Finding 309 (break preserves loop var) — that's about break;
    this is about NORMAL completion
"""


def last_value_after_range(n: int) -> int:
    """Loop variable holds last iterator value after normal completion."""
    i: int = -1  # sentinel
    for i in range(n):
        pass
    # CPython: i == n-1 (last value produced by range)
    # Model (while translation): i == n (incremented past last)
    return i


def last_value_used_in_computation(n: int) -> int:
    """Common pattern: use loop variable after loop for 'last index'."""
    total: int = 0
    i: int = 0
    for i in range(1, n + 1):
        total = total + i
    # CPython: i == n (last value from range(1, n+1))
    # Model: i == n+1 (one past)
    # Using i after loop: total + i should be sum(1..n) + n
    return total + i


def index_after_search(xs: list[int], target: int) -> int:
    """Loop variable after exhaustive search (no break)."""
    i: int = -1
    for i in range(len(xs)):
        if xs[i] == target:
            return i  # early return on found
    # If we reach here, target not found
    # i == len(xs) - 1 (last index checked) in CPython
    # i == len(xs) in model (one past)
    return i  # returns last index, not len(xs)


def range_with_step_final_value() -> int:
    """Step > 1: final value is last value produced, not stop."""
    i: int = -1
    for i in range(0, 10, 3):
        pass
    # range(0, 10, 3) produces: 0, 3, 6, 9
    # CPython: i == 9 (last produced value)
    # Model: depends on translation; may be 12 (9+3) or 10
    return i


def empty_range_variable_unchanged() -> int:
    """Empty range: loop variable retains pre-loop value."""
    i: int = 42
    for i in range(0):  # empty range, no iterations
        pass
    # CPython: i == 42 (loop body never executed, i never assigned)
    # Model (while): i starts at 0, condition 0<0 false, i==0 (WRONG)
    return i


def main() -> None:
    assert last_value_after_range(5) == 4, f"Got {last_value_after_range(5)}"
    assert last_value_after_range(1) == 0, f"Got {last_value_after_range(1)}"

    # sum(1..5) = 15, plus last value 5 = 20
    assert last_value_used_in_computation(5) == 20

    assert range_with_step_final_value() == 9

    assert empty_range_variable_unchanged() == 42

    print("All passed")


main()
