# List equality with length mismatch — `[1,2] == [1,2,3]` must be False;
# recursive comparison without length check may match prefix
"""
Comparing two lists with `==` when they have different lengths should
always return False. In CPython, list equality first checks length,
then compares elements. If the model's PEq on ListAny doesn't check
length first (or has no model at all — finding 040), it may return
True for lists of different lengths if the shorter list's elements
happen to match a prefix of the longer list.
"""


def lists_equal(a: list[int], b: list[int]) -> bool:
    return a == b


def check_prefix(a: list[int], b: list[int]) -> bool:
    """a is a prefix of b but not equal."""
    return a == b


def main() -> None:
    # Same content: equal
    assert lists_equal([1, 2, 3], [1, 2, 3]) == True

    # Different length: NOT equal (even if prefix matches)
    assert lists_equal([1, 2], [1, 2, 3]) == False
    assert lists_equal([1, 2, 3], [1, 2]) == False

    # Empty vs non-empty
    assert lists_equal([], [1]) == False
    assert lists_equal([1], []) == False

    # Both empty: equal
    assert lists_equal([], []) == True

    # Same length, different content
    assert lists_equal([1, 2, 3], [1, 2, 4]) == False

    # Prefix check: [1,2] is prefix of [1,2,3] but NOT equal
    assert check_prefix([1, 2], [1, 2, 3]) == False

    # Single element
    assert lists_equal([5], [5]) == True
    assert lists_equal([5], [6]) == False

    print(lists_equal([1, 2], [1, 2, 3]), lists_equal([1, 2, 3], [1, 2, 3]))


main()
