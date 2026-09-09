# `range(0, 10, 2)` step — must increment by step not 1; if step ignored,
# iterates 10 times instead of 5
"""
FOR RANGE WITH STEP 2 — SKIPS ELEMENTS, ITERATION COUNT IS HALVED

CPython: for i in range(0, 10, 2): → iterates i = 0, 2, 4, 6, 8
         5 iterations, not 10.

Model:   If step is ignored or always 1:
         for i in range(0, 10, 2): → iterates i = 0, 1, 2, ..., 9
         10 iterations (WRONG)

         If step is used but iteration count formula wrong:
         count = (stop - start) // step = (10 - 0) // 2 = 5 (correct)
         But: must also handle non-divisible cases:
         range(0, 7, 2) → [0, 2, 4, 6] → 4 iterations (ceil((7-0)/2) = 4)

CPython result: [0, 2, 4, 6, 8] (5 elements)
Model result: [0, 1, 2, ..., 9] (10 elements, if step ignored)
"""


def even_indices(n: int) -> list[int]:
    """Collect even numbers using step=2."""
    result: list[int] = []
    for i in range(0, n, 2):
        result.append(i)
    return result


def sum_every_third(xs: list[int]) -> int:
    """Sum elements at indices 0, 3, 6, ..."""
    total: int = 0
    i: int = 0
    while i < len(xs):
        total += xs[i]
        i += 3
    return total


def count_range_elements(start: int, stop: int, step: int) -> int:
    """Count iterations of range(start, stop, step)."""
    count: int = 0
    for i in range(start, stop, step):
        count += 1
    return count


def collect_range(start: int, stop: int, step: int) -> list[int]:
    """Collect all elements from range."""
    result: list[int] = []
    for i in range(start, stop, step):
        result.append(i)
    return result


def main() -> None:
    # Test 1: step 2
    assert even_indices(10) == [0, 2, 4, 6, 8]
    assert even_indices(7) == [0, 2, 4, 6]

    # Test 2: step 3 (via while)
    assert sum_every_third([1, 2, 3, 4, 5, 6, 7, 8, 9]) == 1 + 4 + 7  # 12

    # Test 3: count iterations
    assert count_range_elements(0, 10, 2) == 5
    assert count_range_elements(0, 10, 3) == 4  # 0,3,6,9
    assert count_range_elements(0, 10, 5) == 2  # 0,5
    assert count_range_elements(0, 10, 10) == 1  # 0
    assert count_range_elements(0, 10, 11) == 1  # 0

    # Test 4: collect with various steps
    assert collect_range(0, 10, 2) == [0, 2, 4, 6, 8]
    assert collect_range(1, 10, 3) == [1, 4, 7]
    assert collect_range(0, 1, 1) == [0]

    print("all passed")


main()
