# `PEq` on lists uses structural equality without recursive element
# normalization — `[True] == [1]` is False in model, True in CPython
"""
PEq on two ListAny values uses structural equality after normalize_any.
But normalize_any only normalizes the TOP-LEVEL Any value (bool->int,
int-valued float->int). It does NOT recursively normalize list elements.

So from_ListAny(cons(from_bool(true), nil)) != from_ListAny(cons(from_int(1), nil))
structurally, but CPython says [True] == [1] is True (element-wise __eq__).
"""


def compare_bool_int_lists(xs: list[int], ys: list[int]) -> bool:
    # In CPython, list.__eq__ compares element-by-element using ==
    # Each element comparison uses the normal == dispatch
    # True == 1 is True in Python (bool is subclass of int)
    return xs == ys


def main() -> None:
    a: list[int] = [1, 2, 3]
    b: list[int] = [True, 2, 3]
    # CPython: [1,2,3] == [True,2,3] is True
    #   because True == 1 is True (bool.__eq__ inherits int.__eq__)
    # Laurel: PEq(from_ListAny(cons(from_int(1),...)),
    #              from_ListAny(cons(from_bool(true),...)))
    #   normalize_any(from_ListAny(...)) returns from_ListAny(...) unchanged
    #   structural comparison: cons(from_int(1),...) != cons(from_bool(true),...)
    #   Result: False
    result: bool = compare_bool_int_lists(a, b)
    print(result)  # CPython: True, Laurel: False

    # Another case: nested structure
    c: list[int] = [0, 1]
    d: list[int] = [False, True]
    result2: bool = c == d
    print(result2)  # CPython: True, Laurel: False


main()
