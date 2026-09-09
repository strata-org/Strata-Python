# `PEq` on dicts uses structural equality on assoc-list — order-dependent;
# `{'a':1,'b':2} == {'b':2,'a':1}` is False in model, True in CPython
"""
PEq on two DictStrAny values uses structural equality on the association
list representation. But Python dict equality is ORDER-INDEPENDENT:
{'a': 1, 'b': 2} == {'b': 2, 'a': 1} is True.

The model's structural comparison on cons-lists is order-dependent:
cons('a', 1, cons('b', 2, empty)) != cons('b', 2, cons('a', 1, empty))
"""


def dicts_equal_different_order(x: int, y: int) -> bool:
    # Build two dicts with same key-value pairs but different insertion order
    d1: dict[str, int] = {}
    d1["x"] = x
    d1["y"] = y

    d2: dict[str, int] = {}
    d2["y"] = y
    d2["x"] = x

    # CPython: True (dict equality is key-set + value equality, order-independent)
    # Laurel: False (structural equality on assoc lists, order-dependent)
    return d1 == d2


def main() -> None:
    result: bool = dicts_equal_different_order(10, 20)
    print(result)  # CPython: True, Laurel: False

    # Even simpler: dict literals in different order
    a: dict[str, int] = {"x": 1, "y": 2}
    b: dict[str, int] = {"y": 2, "x": 1}
    print(a == b)  # CPython: True, Laurel: False


main()
