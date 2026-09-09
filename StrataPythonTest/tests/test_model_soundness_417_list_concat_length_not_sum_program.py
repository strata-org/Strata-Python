# `len([1,2] + [3,4,5]) == 5` — list concat returns Hole (no case) AND no len
# axiom for concat; blocks list-building verification
"""
LIST CONCATENATION LENGTH NOT SUM OF PARTS

CPython: len([1,2] + [3,4,5]) == 5 (always: 2 + 3 = 5)

Model:   PAdd(from_ListAny(a), from_ListAny(b)) → Hole (finding 074/263)
         Even if list concat IS modeled:
         List_len(List_concat(a, b)) == List_len(a) + List_len(b)
         → UNPROVABLE without axiom

CPython result: 5
Model result: Hole (no list+list case) or unconstrained len

Root cause: PAdd has no (from_ListAny, from_ListAny) case (finding 263),
AND even if it did, no len axiom connects concat to length (finding 088).
"""


def concat_and_check_len() -> bool:
    """len(a + b) == len(a) + len(b)."""
    a: list[int] = [1, 2]
    b: list[int] = [3, 4, 5]
    c: list[int] = a + b
    return len(c) == 5


def build_by_concat() -> list[int]:
    """Build list via concatenation."""
    result: list[int] = []
    result = result + [1]
    result = result + [2]
    result = result + [3]
    return result


def concat_preserves_elements() -> bool:
    """Elements accessible after concat."""
    a: list[int] = [10, 20]
    b: list[int] = [30, 40]
    c: list[int] = a + b
    # c[0] == 10, c[1] == 20, c[2] == 30, c[3] == 40
    return c[0] == 10 and c[2] == 30


def prepend_element(xs: list[int], x: int) -> list[int]:
    """Prepend via concat."""
    return [x] + xs


def main() -> None:
    # Test 1: length is sum
    assert concat_and_check_len()

    # Test 2: build by concat
    built: list[int] = build_by_concat()
    assert built == [1, 2, 3]
    assert len(built) == 3

    # Test 3: elements preserved
    assert concat_preserves_elements()

    # Test 4: prepend
    result: list[int] = prepend_element([2, 3], 1)
    assert result == [1, 2, 3]

    print("all passed")


main()
