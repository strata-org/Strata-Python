# `lst[-1]` → last element; model has no index wrapping; negative index must
# translate to `lst[len(lst)+i]`
"""
NEGATIVE INDEX WRAPS AROUND — lst[-1] IS LAST ELEMENT

CPython: [10, 20, 30][-1] → 30 (last element)
         [10, 20, 30][-2] → 20 (second to last)
         Negative index i means: access at len(lst) + i

Model:   List_get(lst, -1) → either:
         - Hole (no negative index handling)
         - IndexError (treats -1 as out of bounds)
         - Accesses index -1 literally (undefined for cons-list)

CPython result: 30
Model result: Hole or IndexError (WRONG — should be 30)

Root cause: Finding 020 identified this. List_get has no index-wrapping
logic. Negative indices must be translated to: lst[len(lst) + i].
"""


def last_element(xs: list[int]) -> int:
    """Access last element with negative index."""
    return xs[-1]


def second_to_last(xs: list[int]) -> int:
    return xs[-2]


def reverse_access(xs: list[int]) -> list[int]:
    """Access all elements in reverse using negative indices."""
    result: list[int] = []
    i: int = -1
    while i >= -len(xs):
        result.append(xs[i])
        i -= 1
    return result


def swap_first_last(xs: list[int]) -> list[int]:
    """Swap first and last using negative index."""
    if len(xs) < 2:
        return xs
    first: int = xs[0]
    last: int = xs[-1]
    xs[0] = last
    xs[-1] = first
    return xs


def main() -> None:
    data: list[int] = [10, 20, 30, 40, 50]

    # Test 1: last element
    # CPython: 50
    # Model: Hole or error (no negative index wrapping)
    assert last_element(data) == 50

    # Test 2: second to last
    assert second_to_last(data) == 40

    # Test 3: -1 on single element
    assert last_element([99]) == 99

    # Test 4: reverse access
    assert reverse_access([1, 2, 3]) == [3, 2, 1]

    # Test 5: swap first and last
    assert swap_first_last([1, 2, 3]) == [3, 2, 1]

    print("all passed")


main()
