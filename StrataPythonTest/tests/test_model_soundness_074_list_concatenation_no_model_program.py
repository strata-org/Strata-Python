# List concatenation (`[1,2] + [3,4]`) has no model — `PAdd` has no
# `from_ListAny × from_ListAny` case
"""
List concatenation (`[1,2] + [3,4]`) produces a new list containing all
elements of both lists. The model's PAdd dispatches on tags — it handles
int+int, float+float, str+str. But from_ListAny + from_ListAny requires
a List_concat operation that may not exist in the prelude.
"""


def concat_lists(a: list[int], b: list[int]) -> list[int]:
    return a + b


def flatten_pairs(pairs: list[list[int]]) -> list[int]:
    result: list[int] = []
    for p in pairs:
        result = result + p
    return result


def build_range_list(start: int, end: int) -> list[int]:
    result: list[int] = []
    i: int = start
    while i < end:
        result = result + [i]
        i = i + 1
    return result


def main() -> None:
    # Basic concatenation
    a: list[int] = [1, 2, 3]
    b: list[int] = [4, 5, 6]
    c: list[int] = a + b
    assert c == [1, 2, 3, 4, 5, 6]
    assert len(c) == 6

    # Concatenation with empty
    assert a + [] == [1, 2, 3]
    assert [] + b == [4, 5, 6]

    # Flatten
    pairs: list[list[int]] = [[1, 2], [3, 4], [5, 6]]
    flat: list[int] = flatten_pairs(pairs)
    assert flat == [1, 2, 3, 4, 5, 6]

    # Build list incrementally
    built: list[int] = build_range_list(0, 5)
    assert built == [0, 1, 2, 3, 4]

    print(c, len(flat))


main()
