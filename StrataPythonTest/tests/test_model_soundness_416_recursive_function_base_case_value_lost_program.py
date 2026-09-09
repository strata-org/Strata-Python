# Recursive function base case — `factorial(0)` returns 1 but model either
# doesn't terminate return OR recursive call returns Hole
"""
RECURSIVE FUNCTION BASE CASE VALUE LOST

CPython: factorial(0) → 1 (base case returns 1)
         factorial(3) → 6 (3 * 2 * 1 * 1)

Model:   If return doesn't terminate (finding 052/165/344):
         factorial(0): if n <= 1: return 1  ← "return" doesn't stop
                       return n * factorial(n-1)  ← ALSO executes!
         Result: n * factorial(n-1) = 0 * factorial(-1) = ... (infinite or wrong)

         Even if return DOES terminate, the recursive call:
         factorial(n-1) returns unconstrained value (finding 168)
         unless the function is inlined.

CPython result: factorial(3) == 6
Model result: Hole (recursive call returns unconstrained) or wrong value (return doesn't terminate)

Root cause: Either return doesn't terminate (finding 052) OR
recursive call has no postcondition (finding 168).
"""


def factorial(n: int) -> int:
    """Recursive function — the simplest recursive pattern."""
    if n <= 1:
        return 1
    return n * factorial(n - 1)


def fibonacci(n: int) -> int:
    """Double recursion."""
    if n <= 0:
        return 0
    if n == 1:
        return 1
    return fibonacci(n - 1) + fibonacci(n - 2)


def sum_recursive(xs: list[int], i: int) -> int:
    """Recursive list sum."""
    if i >= len(xs):
        return 0
    return xs[i] + sum_recursive(xs, i + 1)


def power(base: int, exp: int) -> int:
    """Recursive power."""
    if exp == 0:
        return 1
    return base * power(base, exp - 1)


def main() -> None:
    # Test 1: factorial
    assert factorial(0) == 1
    assert factorial(1) == 1
    assert factorial(3) == 6
    assert factorial(5) == 120

    # Test 2: fibonacci
    assert fibonacci(0) == 0
    assert fibonacci(1) == 1
    assert fibonacci(5) == 5
    assert fibonacci(7) == 13

    # Test 3: recursive sum
    assert sum_recursive([1, 2, 3, 4], 0) == 10
    assert sum_recursive([], 0) == 0

    # Test 4: power
    assert power(2, 0) == 1
    assert power(2, 3) == 8
    assert power(3, 2) == 9

    print("all passed")


main()
