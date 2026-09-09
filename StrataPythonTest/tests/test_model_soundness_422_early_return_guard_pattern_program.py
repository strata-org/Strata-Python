# Early return guard pattern — `if bad: return -1; return compute()` — if
# return doesn't terminate, guard is overwritten by main logic
"""
EARLY RETURN GUARD PATTERN — MOST COMMON FUNCTION STRUCTURE

CPython: def f(x):
             if x < 0: return -1  # guard
             return x * 2          # main logic

         f(-5) → -1 (guard returns early)
         f(3) → 6 (main logic)

Model:   If return doesn't terminate (finding 052/165):
         f(-5): if -5 < 0: result = -1  # "return" just assigns
                result = -5 * 2 = -10    # ALSO executes!
         Returns -10 instead of -1.

         The guard pattern is THE most common function structure.
         If early return doesn't work, almost no function verifies correctly.

CPython result: f(-5) == -1
Model result: -10 (if return doesn't terminate) or Hole
"""


def safe_divide(a: int, b: int) -> int:
    """Guard: return early if divisor is zero."""
    if b == 0:
        return 0
    return a // b


def abs_value(n: int) -> int:
    """Guard: return early for negative."""
    if n < 0:
        return -n
    return n


def clamp(x: int, lo: int, hi: int) -> int:
    """Two guards: check bounds."""
    if x < lo:
        return lo
    if x > hi:
        return hi
    return x


def find_in_list(xs: list[int], target: int) -> int:
    """Guard: return -1 for empty list."""
    if len(xs) == 0:
        return -1
    for x in xs:
        if x == target:
            return x
    return -1


def validate_and_process(x: int) -> int:
    """Multiple guards before main logic."""
    if x < 0:
        return -1
    if x > 1000:
        return -2
    if x == 0:
        return 0
    return x * x


def main() -> None:
    # Test 1: safe_divide guard
    assert safe_divide(10, 2) == 5
    assert safe_divide(10, 0) == 0  # guard returns 0

    # Test 2: abs guard
    assert abs_value(5) == 5
    assert abs_value(-3) == 3  # guard returns -n

    # Test 3: clamp two guards
    assert clamp(5, 0, 10) == 5
    assert clamp(-5, 0, 10) == 0   # first guard
    assert clamp(15, 0, 10) == 10  # second guard

    # Test 4: find with guard
    assert find_in_list([1, 2, 3], 2) == 2
    assert find_in_list([], 5) == -1  # guard

    # Test 5: multiple guards
    assert validate_and_process(5) == 25
    assert validate_and_process(-1) == -1
    assert validate_and_process(2000) == -2
    assert validate_and_process(0) == 0

    print("all passed")


main()
