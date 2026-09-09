# Negative list indexing (`lst[-1]`) — `List_get` has no index-wrapping logic;
# negative index diverges or returns Hole
"""
Python supports negative list indexing: lst[-1] is the last element,
lst[-2] is second-to-last, etc. The Laurel encoding's List_get function
likely uses the index directly without wrapping negative values, causing
either an out-of-bounds access or returning the wrong element.
"""


def last_element(xs: list[int]) -> int:
    # CPython: xs[-1] wraps to xs[len(xs) - 1]
    return xs[-1]


def second_to_last(xs: list[int]) -> int:
    return xs[-2]


def safe_last(xs: list[int]) -> int:
    # Common pattern: use negative index after length check
    if len(xs) == 0:
        return -1
    return xs[-1]


def main() -> None:
    nums: list[int] = [10, 20, 30, 40, 50]

    a: int = last_element(nums)
    # CPython: nums[-1] = nums[4] = 50
    assert a == 50

    b: int = second_to_last(nums)
    # CPython: nums[-2] = nums[3] = 40
    assert b == 40

    c: int = safe_last(nums)
    assert c == 50

    d: int = safe_last([])
    assert d == -1

    print(a, b, c, d)


main()
