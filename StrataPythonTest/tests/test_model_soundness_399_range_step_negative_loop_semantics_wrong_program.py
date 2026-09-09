# range(start, stop, negative_step) — loop condition must be `i > stop` not `i
# < stop`; wrong direction = wrong iteration count
"""
range() WITH NEGATIVE STEP — LOOP SEMANTICS WRONG

The subset says range(a, b, step) is IN with int arguments.
CPython: range(10, 0, -2) → [10, 8, 6, 4, 2] (counts DOWN)
         range(0, 10, -1) → [] (empty — wrong direction)

Model:   The for-loop translation likely assumes FORWARD iteration:
         while i < stop: body; i += step
         With negative step, this is WRONG:
         - Condition should be i > stop (not i < stop)
         - Or: the range is empty (step goes wrong direction)

Finding 161 mentions this issue. This finding provides the CONCRETE
program showing the model computes wrong iteration counts and values.
"""


def countdown(start: int, stop: int, step: int) -> list[int]:
    """Collect range elements — tests negative step."""
    result: list[int] = []
    for i in range(start, stop, step):
        result.append(i)
    return result


def sum_countdown(n: int) -> int:
    """Sum from n down to 1."""
    total: int = 0
    for i in range(n, 0, -1):
        total += i
    return total


def empty_range_wrong_direction() -> int:
    """range(0, 10, -1) is EMPTY — wrong direction."""
    count: int = 0
    for i in range(0, 10, -1):
        count += 1
    # CPython: count == 0 (empty range)
    # Model (if assumes forward): count == 10 (WRONG)
    return count


def step_two_backward() -> list[int]:
    """range(10, 0, -2) → [10, 8, 6, 4, 2]."""
    result: list[int] = []
    for i in range(10, 0, -2):
        result.append(i)
    return result


def range_length_formula(start: int, stop: int, step: int) -> int:
    """Number of iterations = max(0, ceil((stop-start)/step))."""
    count: int = 0
    for i in range(start, stop, step):
        count += 1
    return count


def main() -> None:
    # Test 1: basic countdown
    assert countdown(5, 0, -1) == [5, 4, 3, 2, 1]

    # Test 2: sum countdown
    assert sum_countdown(5) == 15  # 5+4+3+2+1

    # Test 3: empty range (wrong direction)
    assert empty_range_wrong_direction() == 0

    # Test 4: step -2
    assert step_two_backward() == [10, 8, 6, 4, 2]

    # Test 5: range length formula
    assert range_length_formula(0, 10, 2) == 5   # [0,2,4,6,8]
    assert range_length_formula(10, 0, -2) == 5  # [10,8,6,4,2]
    assert range_length_formula(0, 10, -1) == 0  # empty
    assert range_length_formula(10, 0, 1) == 0   # empty

    print("all passed")


main()
