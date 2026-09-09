# Built-in operations (list index, int()) use preconditions not exceptions;
# `try/except` catching IndexError/ValueError is unreachable in model
"""
Built-in operations (list indexing, dict key access, int()) can raise
exceptions (IndexError, KeyError, ValueError). The Laurel model likely
does not emit exception values for these operations — List_get with an
out-of-bounds index either has a precondition (blocking the path) or
returns Hole, but does NOT set maybe_except to IndexError. This means
try/except blocks that catch built-in exceptions from these operations
are modeled incorrectly: the except branch is unreachable in the model.
"""


def safe_get(xs: list[int], i: int) -> int:
    try:
        return xs[i]
    except IndexError:
        return -1


def safe_parse(s: str) -> int:
    try:
        return int(s)
    except ValueError:
        return 0


def main() -> None:
    nums: list[int] = [10, 20, 30]

    # Valid index: returns the element
    a: int = safe_get(nums, 1)
    assert a == 20

    # Out-of-bounds: CPython raises IndexError, caught by except
    b: int = safe_get(nums, 10)
    assert b == -1

    # Valid parse
    c: int = safe_parse("42")
    assert c == 42

    # Invalid parse: CPython raises ValueError, caught by except
    d: int = safe_parse("hello")
    assert d == 0

    print(a, b, c, d)


main()
