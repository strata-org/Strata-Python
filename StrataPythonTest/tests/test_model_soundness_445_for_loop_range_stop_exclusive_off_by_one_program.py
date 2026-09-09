# `for i in range(n)` stop-exclusivity — model must enforce `i < n` (strict);
# off-by-one if `<=`; critical for `lst[i]` safety in `range(len(lst))`
# pattern
"""
FOR LOOP OVER range() — STOP IS EXCLUSIVE BUT MODEL MAY INCLUDE IT

DIVERGENCE:
  CPython:  `for i in range(n)` iterates i = 0, 1, ..., n-1 (n excluded)
            `for i in range(a, b)` iterates i = a, a+1, ..., b-1 (b excluded)
  Model:    If range is modeled as `0 <= i <= n` (inclusive) instead of
            `0 <= i < n` (exclusive), the loop body executes one extra time.

This is subtle because:
1. The off-by-one only manifests when the loop body uses `i` at the boundary
2. List access `lst[i]` with `for i in range(len(lst))` is safe in CPython
   (i goes 0..len-1) but UNSAFE if model uses inclusive bound (i reaches len)
3. Accumulation loops produce wrong sums if extra iteration included

The model likely translates `for i in range(n)` as:
  i = 0; while i < n: body; i = i + 1
But if the translation uses `<=` instead of `<`, or if the range axioms
don't enforce exclusivity of the stop bound, the model diverges.

ROOT CAUSE: range() stop-exclusivity must be an axiom in the model.
Without it, the solver may consider i == n as a valid loop iteration.
"""


def sum_range_exclusive(n: int) -> int:
    """Sum 0 + 1 + ... + (n-1). Stop is EXCLUSIVE."""
    total: int = 0
    for i in range(n):
        total = total + i
    # CPython: sum of 0..n-1 = n*(n-1)/2
    # Model with inclusive: sum of 0..n = n*(n+1)/2 (WRONG)
    return total


def last_index_safe(lst: list[int]) -> int:
    """Access lst[i] for i in range(len(lst)) — always safe in CPython."""
    total: int = 0
    for i in range(len(lst)):
        # CPython: i goes 0, 1, ..., len-1. lst[i] always valid.
        # Model (if inclusive): i reaches len(lst). lst[len(lst)] is IndexError!
        total = total + lst[i]
    return total


def range_start_stop_exclusive(a: int, b: int) -> int:
    """range(a, b) iterates a, a+1, ..., b-1."""
    count: int = 0
    for i in range(a, b):
        count = count + 1
    # CPython: count == b - a (when b > a)
    # Model (if inclusive): count == b - a + 1 (WRONG)
    return count


def range_boundary_value(n: int) -> int:
    """The value of i after the loop — it's n-1 in CPython (last iteration)."""
    last: int = -1
    for i in range(n):
        last = i
    # CPython: last == n - 1 (last value assigned)
    # Model (if inclusive): last == n (WRONG)
    return last


def range_empty_when_start_equals_stop() -> int:
    """range(5, 5) is empty — zero iterations."""
    count: int = 0
    for i in range(5, 5):
        count = count + 1
    # CPython: count == 0 (empty range)
    # Model (if inclusive): count == 1 (iterates i=5)
    return count


def main() -> None:
    # Test 1: sum of range(5) = 0+1+2+3+4 = 10
    assert sum_range_exclusive(5) == 10
    # NOT 15 (which would be 0+1+2+3+4+5 with inclusive stop)

    # Test 2: safe list access
    assert last_index_safe([10, 20, 30]) == 60

    # Test 3: range(2, 7) has 5 elements
    assert range_start_stop_exclusive(2, 7) == 5

    # Test 4: last iteration value
    assert range_boundary_value(5) == 4  # NOT 5

    # Test 5: empty range
    assert range_empty_when_start_equals_stop() == 0

    print("all passed")


main()
