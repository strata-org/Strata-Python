# `list.pop()` dual return — must return popped element AND rebind list to
# shorter version; no single pure function does both
"""
`list.pop()` removes and returns the last element.
`list.pop(i)` removes and returns element at index i.

Under pure cons-list semantics, pop must:
1. Return the removed element (the expression value)
2. Rebind the list variable to a new list WITHOUT that element

This is a DUAL return: one value goes to the caller (the popped element),
another value replaces the list (the shortened list). No single pure
function naturally returns both.

Similarly, `list.remove(x)` removes the first occurrence of x.
It returns None but modifies the list.

Uses ONLY confirmed-accepted constructs: list, int, function def.
"""


def pop_last(xs: list[int]) -> int:
    """Pop last element — returns it, list shrinks."""
    val: int = xs.pop()
    # xs is now shorter by 1
    # val is the removed element
    return val


def pop_at_index(xs: list[int], i: int) -> int:
    """Pop at specific index."""
    val: int = xs.pop(i)
    return val


def pop_and_check_length(xs: list[int]) -> int:
    """Pop, then verify list length decreased."""
    original_len: int = len(xs)
    xs.pop()
    return original_len - len(xs)  # should be 1


def stack_operations() -> int:
    """Use list as stack with append/pop."""
    stack: list[int] = []
    stack.append(10)
    stack.append(20)
    stack.append(30)
    # stack = [10, 20, 30]
    top: int = stack.pop()  # 30
    second: int = stack.pop()  # 20
    return top + second  # 50


def remove_first_occurrence() -> list[int]:
    """list.remove(x) removes first x, returns None."""
    xs: list[int] = [1, 2, 3, 2, 1]
    xs.remove(2)  # removes first 2
    return xs  # [1, 3, 2, 1]


def main() -> None:
    # Pop last
    data: list[int] = [1, 2, 3, 4, 5]
    val: int = pop_last(data)
    assert val == 5

    # Pop at index
    data2: list[int] = [10, 20, 30, 40]
    val2: int = pop_at_index(data2, 1)
    assert val2 == 20

    # Stack operations
    assert stack_operations() == 50

    # Remove
    result: list[int] = remove_first_occurrence()
    assert result == [1, 3, 2, 1]

    # Pop and check
    data3: list[int] = [7, 8, 9]
    assert pop_and_check_length(data3) == 1

    print(val, stack_operations(), result)


main()
