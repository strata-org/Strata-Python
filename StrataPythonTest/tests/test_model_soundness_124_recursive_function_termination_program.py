# Recursive functions — require bounded unrolling (bug-finding) or
# contracts+termination measures (deductive)
"""
Recursive functions call themselves. The model must handle:
1. The function's translation must allow self-reference
2. Termination: the verifier needs a decreasing measure
3. Stack depth: CPython has a recursion limit (~1000); model is unbounded

If the translator doesn't support recursion (e.g., requires all callees
to be defined before callers), recursive functions can't be translated.
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


def sum_list_recursive(lst: list[int], i: int) -> int:
    if i >= len(lst):
        return 0
    return lst[i] + sum_list_recursive(lst, i + 1)


def power(base: int, exp: int) -> int:
    if exp == 0:
        return 1
    return base * power(base, exp - 1)


def gcd(a: int, b: int) -> int:
    if b == 0:
        return a
    return gcd(b, a % b)


def main() -> None:
    # Factorial
    assert factorial(0) == 1
    assert factorial(1) == 1
    assert factorial(5) == 120

    # Fibonacci
    assert fibonacci(0) == 0
    assert fibonacci(1) == 1
    assert fibonacci(6) == 8

    # Recursive list sum
    assert sum_list_recursive([1, 2, 3, 4, 5], 0) == 15

    # Power
    assert power(2, 10) == 1024

    # GCD
    assert gcd(12, 8) == 4
    assert gcd(17, 5) == 1

    print(factorial(5), fibonacci(6), gcd(12, 8))


main()
