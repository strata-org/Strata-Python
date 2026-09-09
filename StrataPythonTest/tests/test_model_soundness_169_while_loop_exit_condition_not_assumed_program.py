# While loop exit condition not assumed — `assume(!cond)` must be emitted
# after loop; without it, post-loop reasoning is impossible
"""
After a `while` loop exits, the loop condition is FALSE. The model must
assume the negation of the condition after the loop for the solver to
reason about post-loop state.

Example:
    while i < n:
        i = i + 1
    # Here: i >= n (loop condition negated)

Without this assumption, the solver doesn't know WHY the loop exited.
It can't prove that `i >= n` after the loop, making post-loop assertions
unprovable.

Uses ONLY confirmed-accepted constructs: while, int, comparison, function def.
"""


def find_threshold(start: int, limit: int) -> int:
    """Increment until reaching limit."""
    i: int = start
    while i < limit:
        i = i + 1
    # After loop: i >= limit (condition `i < limit` is false)
    assert i >= limit
    return i


def count_to_zero(n: int) -> int:
    """Decrement until non-positive."""
    x: int = n
    while x > 0:
        x = x - 1
    # After loop: x <= 0
    assert x <= 0
    return x


def binary_search_steps(n: int) -> int:
    """Count how many halvings to reach 0."""
    steps: int = 0
    val: int = n
    while val > 1:
        val = val // 2
        steps = steps + 1
    # After loop: val <= 1
    assert val <= 1
    return steps


def drain_list(xs: list[int]) -> int:
    """Process elements until empty (using index)."""
    i: int = 0
    total: int = 0
    while i < len(xs):
        total = total + xs[i]
        i = i + 1
    # After loop: i >= len(xs)
    # Combined with i starting at 0 and incrementing by 1: i == len(xs)
    return total


def main() -> None:
    assert find_threshold(0, 5) == 5
    assert find_threshold(3, 5) == 5
    assert find_threshold(10, 5) == 10  # loop never executes

    assert count_to_zero(5) == 0
    assert count_to_zero(0) == 0  # loop never executes
    assert count_to_zero(-3) == -3  # loop never executes

    assert binary_search_steps(16) == 4  # 16→8→4→2→1
    assert binary_search_steps(1) == 0   # loop never executes

    assert drain_list([1, 2, 3]) == 6
    assert drain_list([]) == 0

    print(find_threshold(0, 5), count_to_zero(5), binary_search_steps(16))


main()
