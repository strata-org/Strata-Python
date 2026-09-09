# While loop exit: `while n>0: n-=1` → post-loop `n==0` unprovable without
# `assume(!(n>0))` after loop
"""
WHILE LOOP EXIT CONDITION — n == 0 AFTER `while n > 0: n -= 1`

CPython: n = 5; while n > 0: n -= 1; assert n == 0 (always true)

Model:   Finding 169 says while-loop exit condition not assumed.
         After the loop, the model should know: not (n > 0) → n <= 0.
         Combined with n starting positive and decrementing by 1:
         n == 0 after the loop.

         But without `assume(not condition)` after the loop,
         the solver treats n as unconstrained post-loop.
         `assert n == 0` is UNPROVABLE.

This is the simplest possible while-loop verification:
a countdown to zero. If the model can't verify this, it can't
verify ANY while loop.
"""


def countdown_to_zero(n: int) -> int:
    """Simplest while loop: decrement to zero."""
    while n > 0:
        n -= 1
    # CPython: n == 0 (loop exits when n <= 0; started positive, decremented by 1)
    # Model without exit assume: n is unconstrained
    return n


def sum_to_n(n: int) -> int:
    """Sum 1..n using while loop."""
    total: int = 0
    i: int = 1
    while i <= n:
        total += i
        i += 1
    # After loop: i == n + 1 (exit condition: not (i <= n) → i > n → i == n+1)
    return total


def find_threshold(xs: list[int], threshold: int) -> int:
    """Find first element above threshold using while + index."""
    i: int = 0
    while i < len(xs):
        if xs[i] > threshold:
            return xs[i]
        i += 1
    # After loop without break: i == len(xs)
    return -1


def gcd(a: int, b: int) -> int:
    """Euclidean GCD — classic while loop."""
    while b != 0:
        temp: int = b
        b = a % b
        a = temp
    # After loop: b == 0, a is the GCD
    return a


def main() -> None:
    # Test 1: countdown
    assert countdown_to_zero(5) == 0
    assert countdown_to_zero(1) == 0
    assert countdown_to_zero(0) == 0

    # Test 2: sum
    assert sum_to_n(5) == 15
    assert sum_to_n(0) == 0

    # Test 3: find threshold
    assert find_threshold([1, 5, 3, 8, 2], 4) == 5
    assert find_threshold([1, 2, 3], 10) == -1

    # Test 4: GCD
    assert gcd(12, 8) == 4
    assert gcd(7, 3) == 1
    assert gcd(10, 0) == 10

    print("all passed")


main()
