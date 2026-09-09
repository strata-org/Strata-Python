# `while` loop with `break` — post-loop `assume(!cond)` is UNSOUND when break
# exits; condition may still be True; model over-constrains
"""
WHILE loop with BREAK — post-loop assume(!cond) is UNSOUND.

When a `while` loop exits via `break`, the loop condition may still be True.
The standard translation emits `assume(!cond)` after the loop to let the
solver reason about post-loop state. But if the loop exited via `break`,
this assumption is FALSE — it introduces unsoundness by assuming something
that doesn't hold.

    while i < n:
        if found(i):
            break
        i = i + 1
    # Model assumes: i >= n (WRONG if break was taken)
    # CPython: i < n is still True (break exited early)

This is distinct from:
- Finding 054 (break/continue not modeled at all)
- Finding 136 (while True: break pattern)
- Finding 169 (exit condition not assumed — MISSING assume)
- Finding 309 (for-loop break preserves variable)

This finding is about the assume being PRESENT but WRONG: it over-constrains
the post-loop state, potentially making the verifier MISS bugs or PROVE
false properties.

Uses ONLY confirmed-accepted constructs: while, break, if, int, comparison.
"""


def find_first_negative(xs: list[int]) -> int:
    """Find index of first negative element, or -1 if none."""
    i: int = 0
    found: int = -1
    while i < len(xs):
        if xs[i] < 0:
            found = i
            break
        i = i + 1
    # CPython: if break was taken, i < len(xs) is STILL TRUE
    # Model with assume(!(i < len(xs))): assumes i >= len(xs) — WRONG
    # This false assumption could let the solver "prove" i >= len(xs)
    # even though i is actually a valid index
    return found


def search_with_postcondition(xs: list[int], target: int) -> bool:
    """Search for target; after loop, check if we found it."""
    i: int = 0
    result: bool = False
    while i < len(xs):
        if xs[i] == target:
            result = True
            break
        i = i + 1
    # If break taken: i < len(xs) AND xs[i] == target
    # Model assumes: i >= len(xs) — contradicts the break path
    # Solver may conclude this path is unreachable (false negative)
    return result


def bounded_search(n: int) -> int:
    """Find first i where i*i > 100, searching up to n."""
    i: int = 0
    while i < n:
        if i * i > 100:
            break
        i = i + 1
    # CPython: if i*i > 100 triggered break, then i < n still holds
    # Model assumes: i >= n — WRONG
    # A subsequent assert(i < n) would be "proved" by the model
    # but would FAIL at runtime if break was taken with i < n
    return i


def break_vs_normal_exit(limit: int) -> int:
    """Demonstrate that break and normal exit have different postconditions."""
    count: int = 0
    while count < limit:
        if count == 5:
            break
        count = count + 1
    # Two possible exits:
    # 1. Normal: count >= limit (condition became false)
    # 2. Break: count == 5 AND count < limit (condition still true)
    #
    # Model with assume(count >= limit): UNSOUND for case 2
    # Model WITHOUT assume: loses information for case 1 (finding 169)
    #
    # Correct encoding needs DISJUNCTION:
    #   assume(count >= limit OR break_was_taken)
    # where break_was_taken carries its own constraints
    return count


def main() -> None:
    xs: list[int] = [3, 7, -2, 5, -1]

    # find_first_negative: break at index 2
    idx: int = find_first_negative(xs)
    assert idx == 2
    # At this point, the loop exited with i=2 < len(xs)=5
    # Model's assume(i >= 5) is FALSE

    # search_with_postcondition
    assert search_with_postcondition(xs, 7) == True
    assert search_with_postcondition(xs, 99) == False

    # bounded_search: i*i > 100 at i=11, if n=20
    result: int = bounded_search(20)
    assert result == 11  # 11*11=121 > 100, broke out
    # Model assumes result >= 20 — WRONG, result is 11

    # break_vs_normal_exit
    assert break_vs_normal_exit(10) == 5   # break at 5 < 10
    assert break_vs_normal_exit(3) == 3    # normal exit at 3 >= 3

    print("All while-break postcondition tests pass")


main()
