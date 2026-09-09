# `for x in range(start, stop, step)` with negative step or empty range —
# model assumes forward-counting loop, diverges on reverse iteration
"""
`for x in range(start, stop, step)` with a negative step iterates in
reverse. `range(5, 0, -1)` yields [5, 4, 3, 2, 1]. `range(5, 5)` yields
nothing. If the model translates `for x in range(a, b)` as a simple
`while x < b` loop without handling negative step or empty ranges, the
iteration count and values diverge from CPython.
"""


def countdown(n: int) -> list[int]:
    result: list[int] = []
    for i in range(n, 0, -1):
        result.append(i)
    # CPython: [n, n-1, ..., 1]
    return result


def sum_reverse_range(start: int, stop: int) -> int:
    total: int = 0
    for i in range(start, stop, -1):
        total = total + i
    return total


def empty_range_sum(a: int, b: int) -> int:
    total: int = 0
    for i in range(a, b):
        total = total + i
    # When a >= b, range is empty, total stays 0
    return total


def step_two(n: int) -> int:
    total: int = 0
    for i in range(0, n, 2):
        total = total + i
    # 0, 2, 4, ... up to but not including n
    return total


def main() -> None:
    # Negative step: countdown
    c: list[int] = countdown(5)
    assert len(c) == 5
    assert c[0] == 5
    assert c[4] == 1

    # Negative step sum: range(10, 5, -1) = [10, 9, 8, 7, 6]
    s1: int = sum_reverse_range(10, 5)
    assert s1 == 40  # 10+9+8+7+6

    # Empty range: start >= stop with positive step
    s2: int = empty_range_sum(5, 3)
    assert s2 == 0  # no iterations

    # Empty range: start == stop
    s3: int = empty_range_sum(5, 5)
    assert s3 == 0  # no iterations

    # Step of 2
    s4: int = step_two(10)
    assert s4 == 20  # 0+2+4+6+8

    # Negative step with start < stop: empty
    s5: int = sum_reverse_range(3, 10)
    # range(3, 10, -1) is EMPTY (start < stop with negative step)
    assert s5 == 0

    print(c, s1, s2, s3, s4, s5)


main()
