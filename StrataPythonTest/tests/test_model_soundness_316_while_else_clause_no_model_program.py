# `while/else` clause — else runs only when no break; model has no conditional
# path for break-vs-normal exit
"""
WHILE/ELSE clause — else runs only when loop exits WITHOUT break.

In CPython, `while cond: ... else: ...` executes the else block ONLY
when the loop exits because the condition became False (normal exit).
If the loop exits via `break`, the else block is SKIPPED.

This is the while-loop analog of finding 065 (for/else). The model
must distinguish two exit paths:
  1. Normal exit (condition False) → execute else
  2. Break exit → skip else

If the model has no conditional path for the else block, it either:
  - Always executes else (wrong when break taken)
  - Never executes else (wrong when loop completes normally)
  - Treats else as dead code (wrong in both cases)

Uses ONLY confirmed-accepted constructs: while, break, else, if, int, bool.
"""


def search_while_else(xs: list[int], target: int) -> str:
    """While/else: else means 'not found'."""
    i: int = 0
    while i < len(xs):
        if xs[i] == target:
            break
        i = i + 1
    else:
        # This runs ONLY if while condition became False (no break)
        return "not found"
    # This runs ONLY if break was taken
    return "found"


def find_factor(n: int) -> int:
    """Find smallest factor > 1, or return n if prime."""
    d: int = 2
    while d * d <= n:
        if n % d == 0:
            break
        d = d + 1
    else:
        # No factor found — n is prime
        return n
    return d


def while_else_with_accumulator(limit: int) -> int:
    """Else block modifies accumulator only on normal exit."""
    total: int = 0
    i: int = 0
    while i < limit:
        if i == 7:
            break
        total = total + i
        i = i + 1
    else:
        # Only reached if i >= limit (no break)
        total = total + 100
    # CPython with limit=5: no break, else runs → total = 0+1+2+3+4+100 = 110
    # CPython with limit=10: break at i=7, else skipped → total = 0+1+2+3+4+5+6 = 21
    # Model (always else): limit=10 → 21+100=121 WRONG
    # Model (never else): limit=5 → 10 WRONG
    return total


def main() -> None:
    # Test 1: target found → break → else skipped
    r1: str = search_while_else([10, 20, 30], 20)
    assert r1 == "found"  # break taken, else skipped

    # Test 2: target not found → normal exit → else runs
    r2: str = search_while_else([10, 20, 30], 99)
    assert r2 == "not found"  # condition became False, else runs

    # Test 3: prime detection
    r3: int = find_factor(7)
    assert r3 == 7  # 7 is prime, else runs, returns n

    r4: int = find_factor(12)
    assert r4 == 2  # 12 has factor 2, break taken

    # Test 4: accumulator with else
    r5: int = while_else_with_accumulator(5)
    assert r5 == 110  # no break, else adds 100

    r6: int = while_else_with_accumulator(10)
    assert r6 == 21  # break at 7, else skipped
