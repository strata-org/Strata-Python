# `min([])`/`max([])` raises ValueError — model returns Hole; empty-list case
# must produce exception not unconstrained value
"""
min()/max() on empty list raises ValueError — model returns Hole.

In CPython:
  min([1, 2, 3])  → 1
  max([1, 2, 3])  → 3
  min([])         → ValueError: min() arg is an empty sequence
  max([])         → ValueError: max() arg is an empty sequence

Finding 026 notes that min/max/abs/sum have no Laurel model (results
are Hole). This finding specifically demonstrates the EXCEPTION case:
calling min()/max() on an empty list MUST produce exception(ValueError),
not Hole. Without this, code that crashes at runtime is silently accepted.

The pattern `min(xs)` where xs might be empty is a common bug that
Frontend should catch. If the model returns Hole instead of an exception,
the verifier cannot detect this error.

Uses ONLY confirmed-accepted constructs: min, max, list, try/except, len.
"""


def min_nonempty(xs: list[int]) -> int:
    """min() on non-empty list returns smallest element."""
    return min(xs)
    # CPython with [3,1,2]: 1
    # Model: Hole (no min model)


def max_nonempty(xs: list[int]) -> int:
    """max() on non-empty list returns largest element."""
    return max(xs)
    # CPython with [3,1,2]: 3
    # Model: Hole


def min_empty_crashes() -> int:
    """min([]) raises ValueError — model must detect this."""
    xs: list[int] = []
    return min(xs)
    # CPython: ValueError: min() arg is an empty sequence
    # Model: Hole — verifier MISSES the crash (unsound)


def max_empty_crashes() -> int:
    """max([]) raises ValueError — same issue."""
    xs: list[int] = []
    return max(xs)
    # CPython: ValueError
    # Model: Hole


def safe_min(xs: list[int]) -> int:
    """Safe pattern: check non-empty before min()."""
    if len(xs) == 0:
        return 0
    return min(xs)
    # CPython: works correctly
    # Model: min still returns Hole even in non-empty branch


def min_in_try_except(xs: list[int]) -> int:
    """Catching ValueError from min() on empty list."""
    try:
        return min(xs)
    except ValueError:
        return -1
    # CPython with []: catches ValueError, returns -1
    # Model: min returns Hole (not exception), handler unreachable


def main() -> None:
    assert min_nonempty([3, 1, 2]) == 1
    assert max_nonempty([3, 1, 2]) == 3
    assert safe_min([5, 2, 8]) == 2
    assert safe_min([]) == 0

    # These crash in CPython:
    try:
        min_empty_crashes()
        assert False
    except ValueError:
        pass  # expected

    try:
        max_empty_crashes()
        assert False
    except ValueError:
        pass  # expected

    assert min_in_try_except([1, 2]) == 1
    assert min_in_try_except([]) == -1
