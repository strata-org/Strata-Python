# List `in` with bool/int coercion — `True in [1,2,3]` is True in CPython;
# structural equality says False
"""
`x in lst` for a list of ints uses `==` for comparison. In CPython,
`1 in [True, 2, 3]` is True because `True == 1`. The model's
List_contains uses structural equality on Any values, where
`from_bool(true) != from_int(1)` structurally (finding 013).

This finding provides a concrete program demonstrating the divergence
with a practical pattern: checking membership in a list of constants.
"""


def is_valid_status(code: int) -> bool:
    valid: list[int] = [200, 201, 204, 301, 302]
    return code in valid


def contains_zero(lst: list[int]) -> bool:
    return 0 in lst


def has_value(lst: list[int], target: int) -> bool:
    return target in lst


def remove_duplicates_ordered(lst: list[int]) -> list[int]:
    seen: list[int] = []
    result: list[int] = []
    for x in lst:
        if x not in seen:
            seen = seen + [x]
            result = result + [x]
    return result


def main() -> None:
    # Basic membership
    assert is_valid_status(200) == True
    assert is_valid_status(404) == False

    # Contains zero
    assert contains_zero([1, 2, 0, 3]) == True
    assert contains_zero([1, 2, 3]) == False

    # Generic membership
    assert has_value([10, 20, 30], 20) == True
    assert has_value([10, 20, 30], 25) == False

    # Remove duplicates using `in`
    deduped: list[int] = remove_duplicates_ordered([1, 2, 3, 2, 1, 4])
    assert deduped == [1, 2, 3, 4]

    # The bool/int equivalence case (finding 013)
    mixed: list[int] = [1, 2, 3]
    assert (True in mixed) == True   # True == 1, so True is "in" [1,2,3]
    assert (False in mixed) == False  # False == 0, 0 not in [1,2,3]

    print(is_valid_status(200), has_value([1, 2, 3], 2), len(deduped))


main()
