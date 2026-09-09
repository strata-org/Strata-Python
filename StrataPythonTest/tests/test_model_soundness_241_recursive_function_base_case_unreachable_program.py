# Recursive function base case — return must terminate frame (finding 165);
# without it, recursion is infinite past base case
"""
Recursive functions with a base case that returns early. The model must
handle recursion correctly: the base case terminates, recursive calls
eventually reach the base case.

Under bounded unrolling (finding 124), the verifier unrolls N times.
If the base case is unreachable within N unrollings, the verifier
can't prove termination or correctness.

But more fundamentally: the RETURN in the base case must terminate
that call frame (finding 165). If return doesn't terminate, the
recursive call continues past the base case — infinite recursion.

Uses ONLY Frontend-subset features: function def, int, if, return, recursion.
"""


def factorial(n: int) -> int:
    if n <= 1:
        return 1
    return n * factorial(n - 1)


def fibonacci(n: int) -> int:
    if n <= 0:
        return 0
    if n == 1:
        return 1
    return fibonacci(n - 1) + fibonacci(n - 2)


def sum_to_n(n: int) -> int:
    if n <= 0:
        return 0
    return n + sum_to_n(n - 1)


def power(base: int, exp: int) -> int:
    if exp == 0:
        return 1
    return base * power(base, exp - 1)


def gcd(a: int, b: int) -> int:
    if b == 0:
        return a
    return gcd(b, a % b)


def main() -> None:
    assert factorial(5) == 120
    assert factorial(0) == 1
    assert factorial(1) == 1

    assert fibonacci(6) == 8
    assert fibonacci(0) == 0
    assert fibonacci(1) == 1

    assert sum_to_n(10) == 55
    assert sum_to_n(0) == 0

    assert power(2, 10) == 1024
    assert power(3, 0) == 1

    assert gcd(12, 8) == 4
    assert gcd(7, 0) == 7

    print(factorial(5), fibonacci(6), gcd(12, 8))


main()
