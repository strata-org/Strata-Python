# List literal construction cons-order — translator may build cons-list
# reversed; `[1,2,3][0]` returns 3 instead of 1
"""
A list literal `[1, 2, 3]` must be translated to a ListAny cons-list
with elements in the correct order. If built as cons(1, cons(2, cons(3, nil))),
then List_get(lst, 0) must return 1 (not 3). The cons-list's head is
the FIRST element, not the last.

If the translator builds the cons-list in reverse order (cons(3, cons(2, cons(1, nil)))),
then lst[0] returns 3 instead of 1.
"""


def first_element(lst: list[int]) -> int:
    return lst[0]


def last_element(lst: list[int]) -> int:
    return lst[len(lst) - 1]


def check_order(lst: list[int]) -> bool:
    """Verify elements are in declared order."""
    return lst[0] == 10 and lst[1] == 20 and lst[2] == 30


def sum_first_two(lst: list[int]) -> int:
    return lst[0] + lst[1]


def main() -> None:
    data: list[int] = [10, 20, 30, 40, 50]

    # Element order must match literal order
    assert data[0] == 10
    assert data[1] == 20
    assert data[2] == 30
    assert data[3] == 40
    assert data[4] == 50

    # First and last
    assert first_element(data) == 10
    assert last_element(data) == 50

    # Order check
    assert check_order([10, 20, 30]) == True

    # Arithmetic on specific positions
    assert sum_first_two([5, 7, 9]) == 12

    # Single element
    single: list[int] = [42]
    assert single[0] == 42

    # Two elements: order matters
    pair: list[int] = [100, 200]
    assert pair[0] == 100
    assert pair[1] == 200

    print(data[0], data[4], check_order([10, 20, 30]))


main()
