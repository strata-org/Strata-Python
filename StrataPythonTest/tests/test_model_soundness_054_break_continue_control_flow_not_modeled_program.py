# `break`/`continue` may not terminate/skip correctly — if translated like
# `raise` (silently dropped), loop control flow is wrong
"""
Python's `break` statement exits the innermost enclosing loop immediately.
Code after the break within the loop body is unreachable. If the model
doesn't terminate the loop iteration on `break`, subsequent statements
execute and the loop may continue iterating.

Similarly, `continue` skips the rest of the current iteration and jumps
to the loop's next iteration check. If not modeled as a control-flow
jump, code after `continue` executes incorrectly.
"""


def find_index(xs: list[int], target: int) -> int:
    idx: int = -1
    i: int = 0
    for x in xs:
        if x == target:
            idx = i
            break
        i = i + 1
    # CPython: i stops incrementing after break
    # Model without break: i increments for all elements
    return idx


def sum_skip_negatives(xs: list[int]) -> int:
    total: int = 0
    for x in xs:
        if x < 0:
            continue
        total = total + x
    # CPython: negatives are skipped
    # Model without continue: all elements added
    return total


def first_above_threshold(xs: list[int], threshold: int) -> int:
    result: int = -1
    for x in xs:
        if x > threshold:
            result = x
            break
        # Code here should NOT execute after break
        result = 0  # sentinel: if break works, this doesn't overwrite
    return result


def main() -> None:
    # find_index: break stops iteration
    assert find_index([10, 20, 30, 40], 30) == 2
    assert find_index([10, 20, 30, 40], 99) == -1

    # sum_skip_negatives: continue skips rest of body
    assert sum_skip_negatives([1, -2, 3, -4, 5]) == 9

    # first_above_threshold: break prevents overwrite
    r: int = first_above_threshold([1, 2, 10, 3], 5)
    assert r == 10  # NOT 0 (the sentinel after break)

    print(find_index([10, 20, 30, 40], 30),
          sum_skip_negatives([1, -2, 3, -4, 5]),
          r)


main()
