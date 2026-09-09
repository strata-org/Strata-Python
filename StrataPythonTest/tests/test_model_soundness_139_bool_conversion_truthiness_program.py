# `bool()` conversion — full truthiness dispatch needed: `bool(0)==False`,
# `bool("")==False`, `bool([])==False`
"""
`bool(x)` converts any value to True/False using truthiness rules:
- bool(0) == False, bool(nonzero) == True
- bool("") == False, bool(nonempty) == True
- bool([]) == False, bool(nonempty_list) == True
- bool(None) == False

This is IN (builtin conversion) but the model's `Any_to_bool` may not
handle all tags correctly (finding 016 covers ClassInstance; this covers
the full dispatch).
"""


def to_bool_int(x: int) -> bool:
    return bool(x)


def to_bool_str(s: str) -> bool:
    return bool(s)


def to_bool_list(lst: list[int]) -> bool:
    return bool(lst)


def count_truthy(values: list[int]) -> int:
    count: int = 0
    for v in values:
        if bool(v):
            count = count + 1
    return count


def main() -> None:
    # int truthiness
    assert to_bool_int(0) == False
    assert to_bool_int(1) == True
    assert to_bool_int(-1) == True
    assert to_bool_int(42) == True

    # str truthiness
    assert to_bool_str("") == False
    assert to_bool_str("hello") == True
    assert to_bool_str(" ") == True  # space is truthy

    # list truthiness
    assert to_bool_list([]) == False
    assert to_bool_list([1]) == True

    # None
    assert bool(None) == False

    # Count truthy
    assert count_truthy([0, 1, 0, 2, 0, 3]) == 3

    print(to_bool_int(0), to_bool_str(""), count_truthy([0, 1, 2]))


main()
