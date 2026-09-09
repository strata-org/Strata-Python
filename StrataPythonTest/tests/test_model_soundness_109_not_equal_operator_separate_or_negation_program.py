# `!=` operator — may not be handled; needs either separate `PNe` or
# translation as `not (a == b)`
"""
Python's `!=` operator is NOT simply `not (a == b)`. It's a separate
operator (`__ne__`) that can be independently defined. For built-in
types, `a != b` is equivalent to `not (a == b)`, but the model must
either:
1. Have a separate PNe operator, or
2. Translate `!=` as `PNot(PEq(a, b))`

If neither exists, `!=` comparisons return Hole.
"""


def not_equal_ints(a: int, b: int) -> bool:
    return a != b


def not_equal_strs(a: str, b: str) -> bool:
    return a != b


def not_equal_none(x: int) -> bool:
    return x != None  # type: ignore


def filter_not_equal(xs: list[int], target: int) -> list[int]:
    result: list[int] = []
    for x in xs:
        if x != target:
            result = result + [x]
    return result


def all_different(a: int, b: int, c: int) -> bool:
    return a != b and b != c and a != c


def main() -> None:
    # Basic != on ints
    assert not_equal_ints(1, 2) == True
    assert not_equal_ints(5, 5) == False

    # != on strings
    assert not_equal_strs("hello", "world") == True
    assert not_equal_strs("same", "same") == False

    # != with None
    assert not_equal_none(0) == True
    assert (None != None) == False

    # Filter using !=
    filtered: list[int] = filter_not_equal([1, 2, 3, 2, 4, 2], 2)
    assert filtered == [1, 3, 4]

    # All different
    assert all_different(1, 2, 3) == True
    assert all_different(1, 2, 1) == False

    print(not_equal_ints(1, 2), not_equal_strs("a", "b"), len(filtered))


main()
