# `list.append()` returns None not new list — dual requirement: rebind list
# variable AND set expression value to `from_None()`
"""
In CPython, `list.append(x)` returns None (not the modified list).
The mutation happens IN PLACE on the list object.

Under value semantics, the translator must model append as:
    lst = List_append(lst, x)  # rebind to new list

But the RETURN VALUE of append must be from_None(), not the new list.
If the model returns the new list from append, code like:

    result = lst.append(x)
    # result should be None, not the list

would get the wrong value. And if the model doesn't rebind lst:

    lst.append(x)
    # lst should now contain x

the list doesn't grow (finding 009).

The dual requirement: rebind the list AND return None.

Uses ONLY confirmed-accepted constructs: list, append, None, int.
"""


def append_returns_none(lst: list[int], x: int) -> bool:
    result = lst.append(x)
    # result is None in CPython
    return result is None


def append_modifies_list(xs: list[int]) -> int:
    xs.append(10)
    xs.append(20)
    # xs now has 2 more elements
    return len(xs)


def build_list_with_append() -> list[int]:
    result: list[int] = []
    result.append(1)
    result.append(2)
    result.append(3)
    return result


def append_in_loop(n: int) -> list[int]:
    result: list[int] = []
    i: int = 0
    while i < n:
        result.append(i)
        i = i + 1
    return result


def dont_chain_append() -> bool:
    """Common bug: trying to chain append (returns None, not list)."""
    xs: list[int] = []
    # xs.append(1).append(2) would crash: None has no .append
    # Correct usage:
    xs.append(1)
    xs.append(2)
    return len(xs) == 2


def main() -> None:
    # append returns None
    assert append_returns_none([1, 2], 3) == True

    # append modifies the list
    assert append_modifies_list([1, 2, 3]) == 5  # 3 + 2

    # build list
    built: list[int] = build_list_with_append()
    assert built == [1, 2, 3]
    assert len(built) == 3

    # append in loop
    assert append_in_loop(4) == [0, 1, 2, 3]
    assert len(append_in_loop(0)) == 0

    # no chaining
    assert dont_chain_append() == True

    print(append_returns_none([1], 2), len(build_list_with_append()),
          len(append_in_loop(3)))


main()
