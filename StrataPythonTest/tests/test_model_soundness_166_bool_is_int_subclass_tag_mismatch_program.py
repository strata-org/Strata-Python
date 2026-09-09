# Bool-is-int subclass — systematic tag mismatch; `from_bool` must normalize
# to `from_int` for ALL arithmetic/comparison/indexing
"""
Python's bool is a subclass of int: True == 1, False == 0.
The `Any` datatype has SEPARATE tags: from_bool(b) vs from_int(n).

This causes pervasive mismatches when bool values flow into int contexts:
- `True + 1` → 2 in CPython (bool promotes to int)
- In model: PAdd(from_bool(True), from_int(1)) → Hole (tag mismatch)

Finding 018 identified bool arithmetic. Finding 043 identified bool indexing.
Finding 148 identified isinstance. This finding consolidates the ROOT CAUSE:
the two-tag design means EVERY operation that accepts int must ALSO accept
bool, because Python guarantees bool IS int.

The fix must be systematic: either normalize from_bool to from_int at
every operation boundary, or merge the tags entirely.
"""


def bool_as_counter(flags: list[bool]) -> int:
    """Sum of bools — extremely common pattern."""
    total: int = 0
    for f in flags:
        total = total + f  # bool + int: True→1, False→0
    return total


def bool_in_arithmetic(a: bool, b: int) -> int:
    return a + b  # True + 5 = 6


def bool_subtraction(a: int, b: bool) -> int:
    return a - b  # 10 - True = 9


def bool_multiplication(a: bool, b: int) -> int:
    return a * b  # True * 7 = 7, False * 7 = 0


def bool_as_index(lst: list[str], flag: bool) -> str:
    # True → index 1, False → index 0
    return lst[flag]


def bool_comparison_with_int(x: bool, n: int) -> bool:
    return x < n  # True < 2 → True (1 < 2)


def conditional_increment(value: int, should_add: bool) -> int:
    # Idiomatic: value + should_add instead of if/else
    return value + should_add


def main() -> None:
    # Bool as counter
    assert bool_as_counter([True, False, True, True]) == 3
    assert bool_as_counter([False, False]) == 0

    # Bool + int
    assert bool_in_arithmetic(True, 5) == 6
    assert bool_in_arithmetic(False, 5) == 5

    # Int - bool
    assert bool_subtraction(10, True) == 9
    assert bool_subtraction(10, False) == 10

    # Bool * int
    assert bool_multiplication(True, 7) == 7
    assert bool_multiplication(False, 7) == 0

    # Bool as index
    assert bool_as_index(["no", "yes"], True) == "yes"
    assert bool_as_index(["no", "yes"], False) == "no"

    # Bool < int
    assert bool_comparison_with_int(True, 2) == True
    assert bool_comparison_with_int(True, 1) == False  # 1 < 1 is False

    # Conditional increment
    assert conditional_increment(10, True) == 11
    assert conditional_increment(10, False) == 10

    print(bool_as_counter([True, True, False]),
          bool_in_arithmetic(True, 5),
          bool_as_index(["no", "yes"], True))


main()
