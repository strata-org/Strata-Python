# `not in` operator may not be wired — `NotIn` is a separate AST op from `In`;
# translator may not handle it
"""
Python has `not in` as a distinct operator: `x not in lst` is equivalent
to `not (x in lst)` but is a single AST node (Compare with NotIn op).
The model may handle `in` (PIn/List_contains) but not `not in`. If the
translator doesn't recognize NotIn, it either fails or produces Hole.
"""


def is_missing(xs: list[int], target: int) -> bool:
    return target not in xs


def is_new_key(d: dict[str, int], key: str) -> bool:
    return key not in d


def filter_exclude(xs: list[int], exclude: list[int]) -> list[int]:
    result: list[int] = []
    for x in xs:
        if x not in exclude:
            result = result + [x]
    return result


def unique_keys(keys: list[str], existing: dict[str, int]) -> list[str]:
    result: list[str] = []
    for k in keys:
        if k not in existing:
            result = result + [k]
    return result


def main() -> None:
    data: list[int] = [1, 2, 3, 4, 5]

    # not in on list
    assert is_missing(data, 6) == True
    assert is_missing(data, 3) == False

    # not in on dict
    d: dict[str, int] = {"a": 1, "b": 2}
    assert is_new_key(d, "c") == True
    assert is_new_key(d, "a") == False

    # Filter using not in
    filtered: list[int] = filter_exclude([1, 2, 3, 4, 5], [2, 4])
    assert filtered == [1, 3, 5]

    # Unique keys
    new_keys: list[str] = unique_keys(["a", "b", "c", "d"], d)
    assert new_keys == ["c", "d"]

    print(is_missing(data, 6), filtered, new_keys)


main()
