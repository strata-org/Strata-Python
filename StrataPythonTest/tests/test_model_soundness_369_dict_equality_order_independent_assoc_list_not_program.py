# Dict equality order-independent but assoc-list comparison is ordered —
# `{"a":1,"b":2} == {"b":2,"a":1}` returns False in model
"""
DICT EQUALITY IS ORDER-INDEPENDENT — ASSOC-LIST COMPARISON IS NOT

CPython: {"a": 1, "b": 2} == {"b": 2, "a": 1} → True
         Dict equality checks same keys with same values, regardless of
         insertion order.

Model:   PEq on from_DictStrAny uses STRUCTURAL equality on the assoc-list.
         [("a",1), ("b",2)] ≠ [("b",2), ("a",1)] structurally.
         Model returns False when CPython returns True.

Finding 041 identified this issue. This finding provides the CONCRETE
program showing the practical impact: dicts built in different orders
but with same content are not recognized as equal.
"""


def same_content_different_order() -> bool:
    """Two dicts with same k/v pairs, different insertion order."""
    d1: dict[str, int] = {}
    d1["a"] = 1
    d1["b"] = 2

    d2: dict[str, int] = {}
    d2["b"] = 2
    d2["a"] = 1

    # CPython: d1 == d2 → True (same keys, same values)
    # Model: structural comparison of assoc-lists → False (different order)
    return d1 == d2


def literal_vs_built() -> bool:
    """Literal dict vs incrementally built dict."""
    literal: dict[str, int] = {"x": 10, "y": 20}

    built: dict[str, int] = {}
    built["y"] = 20
    built["x"] = 10

    # Same content, different construction order
    return literal == built


def function_returns_equivalent() -> bool:
    """Two functions building same dict differently."""
    d1: dict[str, int] = {"name": 1, "age": 2, "city": 3}
    d2: dict[str, int] = {"city": 3, "name": 1, "age": 2}
    return d1 == d2


def dict_in_condition(a: dict[str, int], b: dict[str, int]) -> str:
    """Using dict equality in control flow."""
    if a == b:
        return "equal"
    return "different"


def main() -> None:
    # Test 1: same content, different order
    assert same_content_different_order()

    # Test 2: literal vs built
    assert literal_vs_built()

    # Test 3: different construction
    assert function_returns_equivalent()

    # Test 4: in condition
    d1: dict[str, int] = {"a": 1, "b": 2}
    d2: dict[str, int] = {"b": 2, "a": 1}
    assert dict_in_condition(d1, d2) == "equal"

    # Test 5: actually different dicts
    d3: dict[str, int] = {"a": 1, "b": 99}
    assert dict_in_condition(d1, d3) == "different"

    print("all passed")


main()
