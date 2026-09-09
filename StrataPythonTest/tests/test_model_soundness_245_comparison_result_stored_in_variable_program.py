# Comparison result stored in variable — `flag = x > 0; if flag:` requires PGt
# to return from_bool; wrong tag breaks later boolean ops
"""
Storing a comparison result in a bool variable, then using it later.
The model must ensure comparisons return `from_bool` (finding 110)
AND that the stored value retains its type for later use.

    flag: bool = x > 0
    if flag:
        ...

The variable `flag` must be `from_bool(True/False)`. If PLt/PGt returns
a wrong tag (from_int(1)) or Hole, then `if flag` fails because
`Any_to_bool` doesn't handle the wrong tag.

Uses ONLY Frontend-subset features: bool, int, comparison, if, and.
"""


def store_comparison(x: int) -> bool:
    result: bool = x > 0
    return result


def use_stored_comparison(x: int, y: int) -> int:
    x_positive: bool = x > 0
    y_positive: bool = y > 0
    if x_positive and y_positive:
        return x + y
    return 0


def comparison_in_variable_then_branch(xs: list[int]) -> int:
    """Store comparison, use in later branch."""
    has_elements: bool = len(xs) > 0
    if has_elements:
        return xs[0]
    return -1


def multiple_comparisons_stored(a: int, b: int, c: int) -> int:
    ab: bool = a < b
    bc: bool = b < c
    if ab and bc:
        return 1  # a < b < c (sorted)
    return 0


def negate_stored_bool(x: int) -> bool:
    positive: bool = x > 0
    return not positive


def bool_from_equality(a: int, b: int) -> bool:
    equal: bool = a == b
    return equal


def main() -> None:
    assert store_comparison(5) == True
    assert store_comparison(-3) == False
    assert store_comparison(0) == False

    assert use_stored_comparison(3, 4) == 7
    assert use_stored_comparison(-1, 4) == 0

    assert comparison_in_variable_then_branch([10, 20]) == 10
    assert comparison_in_variable_then_branch([]) == -1

    assert multiple_comparisons_stored(1, 2, 3) == 1
    assert multiple_comparisons_stored(1, 3, 2) == 0

    assert negate_stored_bool(5) == False
    assert negate_stored_bool(-5) == True

    assert bool_from_equality(3, 3) == True
    assert bool_from_equality(3, 4) == False

    print(store_comparison(5), use_stored_comparison(3, 4),
          negate_stored_bool(5))


main()
