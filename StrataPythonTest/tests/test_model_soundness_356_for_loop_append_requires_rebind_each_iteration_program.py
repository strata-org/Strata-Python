# For-loop append requires rebind each iteration — `result.append(x)` in loop
# body must thread rebound list as loop state; without it list stays empty
"""
FOR LOOP APPEND REQUIRES REBIND EACH ITERATION

CPython: result = []; for x in xs: result.append(x*2)
         After loop: result == [2, 4, 6]
         append() mutates result in place each iteration.

Model:   Lists are pure. append returns a NEW list.
         result.append(x*2) must translate to:
           result = List_append(result, x*2)  // REBIND each iteration
         Without rebinding, result stays empty forever.

         The key issue: the translator must recognize that .append()
         in a for-loop body requires the variable to be REBOUND on
         every iteration. The loop variable `result` must be threaded
         through the loop as mutable state.

This is the MOST COMMON list-building pattern in Python.
Finding 170 covers append returning None.
Finding 154 covers while-loop list growth.
This finding covers the FOR-LOOP + APPEND combination specifically.
"""


def double_all(xs: list[int]) -> list[int]:
    result: list[int] = []
    for x in xs:
        result.append(x * 2)
    return result


def filter_positive(xs: list[int]) -> list[int]:
    result: list[int] = []
    for x in xs:
        if x > 0:
            result.append(x)
    return result


def collect_indices(xs: list[int], target: int) -> list[int]:
    indices: list[int] = []
    i: int = 0
    for x in xs:
        if x == target:
            indices.append(i)
        i += 1
    return indices


def main() -> None:
    # Test 1: map pattern
    data: list[int] = [1, 2, 3]
    result: list[int] = double_all(data)
    # CPython: [2, 4, 6]
    # Model without rebind: [] (append is no-op, result never grows)
    assert result == [2, 4, 6]
    assert len(result) == 3

    # Test 2: filter pattern
    mixed: list[int] = [-1, 2, -3, 4, -5]
    pos: list[int] = filter_positive(mixed)
    # CPython: [2, 4]
    # Model without rebind: []
    assert pos == [2, 4]

    # Test 3: collect pattern
    items: list[int] = [5, 3, 5, 7, 5]
    idx: list[int] = collect_indices(items, 5)
    # CPython: [0, 2, 4]
    # Model without rebind: []
    assert idx == [0, 2, 4]

    print(result)
    print(pos)
    print(idx)


main()
