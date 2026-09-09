# While loop counter `i==n` after `while i<n: i+=1` — exit assume gives `i>=n`
# but precise `i==n` needs loop invariant
"""
WHILE LOOP COUNTER FINAL VALUE — i == n AFTER `while i < n: i += 1`

CPython: i = 0; while i < n: i += 1; assert i == n (always true for n >= 0)

Model:   Without loop exit assume (finding 169/401):
         i is unconstrained after loop → i == n unprovable.

         WITH loop exit assume: assume(!(i < n)) → assume(i >= n)
         But we also need: i was incremented by 1 each iteration,
         started at 0, so i == n (not just i >= n).

         The PRECISE post-loop value requires EITHER:
         - Loop invariant: i >= 0 && i <= n
         - OR: bounded unrolling (for small n)
         - OR: the exit condition alone (i >= n) + knowledge that
           i was < n at the START of the last iteration → i == n

This is the FUNDAMENTAL while-loop verification challenge.
"""


def count_to_n(n: int) -> int:
    """Count from 0 to n."""
    i: int = 0
    while i < n:
        i += 1
    # CPython: i == n (for n >= 0)
    # Model: i >= n (from exit condition) but not necessarily == n
    return i


def sum_1_to_n(n: int) -> int:
    """Sum 1..n with while loop."""
    total: int = 0
    i: int = 1
    while i <= n:
        total += i
        i += 1
    # After: i == n + 1, total == n*(n+1)/2
    return total


def multiply_by_addition(a: int, b: int) -> int:
    """a * b via repeated addition."""
    result: int = 0
    i: int = 0
    while i < b:
        result += a
        i += 1
    # After: i == b, result == a * b
    return result


def power_by_multiplication(base: int, exp: int) -> int:
    """base ** exp via repeated multiplication."""
    result: int = 1
    i: int = 0
    while i < exp:
        result *= base
        i += 1
    return result


def main() -> None:
    # Test 1: count to n
    assert count_to_n(5) == 5
    assert count_to_n(0) == 0
    assert count_to_n(1) == 1

    # Test 2: sum
    assert sum_1_to_n(5) == 15
    assert sum_1_to_n(0) == 0

    # Test 3: multiply
    assert multiply_by_addition(3, 4) == 12
    assert multiply_by_addition(7, 0) == 0

    # Test 4: power
    assert power_by_multiplication(2, 3) == 8
    assert power_by_multiplication(5, 0) == 1

    print("all passed")


main()
