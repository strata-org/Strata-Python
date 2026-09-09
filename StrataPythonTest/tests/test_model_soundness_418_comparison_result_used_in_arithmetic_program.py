# Comparison result in arithmetic — `(x>0) + (y>0)` counts positives;
# from_bool + from_bool has no case; needs bool→int normalization
"""
COMPARISON RESULT USED IN ARITHMETIC — bool + int INTERACTION

CPython: (x > 0) + (y > 0) → counts how many are positive (0, 1, or 2)
         True + True == 2, True + False == 1, False + False == 0

Model:   PGt(x, 0) returns from_bool(True/False)
         PAdd(from_bool(True), from_bool(True)) → Hole (finding 261)
         OR: PAdd returns from_bool (wrong type — should be from_int(2))

CPython result: 2 (int)
Model result: Hole or from_bool(True) (wrong type)

Root cause: Comparison returns from_bool, but arithmetic on bools
requires promotion to int (finding 166/261). The CHAIN is:
comparison → from_bool → promote to from_int → arithmetic.
"""


def count_positive(a: int, b: int, c: int) -> int:
    """Count how many values are positive using bool arithmetic."""
    return (a > 0) + (b > 0) + (c > 0)


def count_flags(flags: list[bool]) -> int:
    """Sum of bools = count of True values."""
    total: int = 0
    for f in flags:
        total += f  # True adds 1, False adds 0
    return total


def weighted_score(passed: bool, bonus: bool) -> int:
    """Bool in arithmetic expression."""
    return passed * 10 + bonus * 5


def conditional_increment(x: int, condition: bool) -> int:
    """x + condition — adds 1 if True, 0 if False."""
    return x + condition


def main() -> None:
    # Test 1: count positives
    assert count_positive(1, -2, 3) == 2
    assert count_positive(-1, -2, -3) == 0
    assert count_positive(1, 2, 3) == 3

    # Test 2: sum of bools
    assert count_flags([True, False, True, True]) == 3
    assert count_flags([False, False]) == 0

    # Test 3: weighted score
    assert weighted_score(True, True) == 15
    assert weighted_score(True, False) == 10
    assert weighted_score(False, False) == 0

    # Test 4: conditional increment
    assert conditional_increment(5, True) == 6
    assert conditional_increment(5, False) == 5

    print("all passed")


main()
