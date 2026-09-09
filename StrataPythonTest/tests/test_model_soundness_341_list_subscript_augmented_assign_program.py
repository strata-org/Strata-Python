# `lst[i] += v` augmented assign on list subscript — requires List_get + PAdd
# + List_set (cons rebuild) + rebind; likely no-op
"""
AUGMENTED ASSIGNMENT ON LIST SUBSCRIPT: lst[i] += v

CPython: lst[i] += v desugars to lst[i] = lst[i] + v (mutates list in place)
Model:   Requires: List_get → PAdd → List_set → rebind lst
         But cons-list List_set requires FULL REBUILD of the list.
         If translator doesn't handle Subscript target in AugAssign for lists,
         the operation is a no-op.

Distinct from finding 336 (dict subscript) because:
- List uses cons-list (O(n) rebuild) vs dict assoc-list
- List needs integer index bounds checking
- List_set semantics differ from DictStrAny_set
"""


def increment_all(xs: list[int]) -> list[int]:
    i: int = 0
    while i < len(xs):
        xs[i] += 1  # augmented assign on list subscript
        i += 1
    return xs


def scale_element(xs: list[int], idx: int, factor: int) -> list[int]:
    xs[idx] *= factor  # another augmented assign variant
    return xs


def accumulate_running(xs: list[int]) -> list[int]:
    i: int = 1
    while i < len(xs):
        xs[i] += xs[i - 1]  # prefix sum pattern
        i += 1
    return xs


def main() -> None:
    # Test 1: increment all elements
    data: list[int] = [10, 20, 30]
    result: list[int] = increment_all(data)
    # CPython: [11, 21, 31]
    # Model: [10, 20, 30] (augmented assign is no-op)
    assert result == [11, 21, 31]

    # Test 2: scale single element
    data2: list[int] = [1, 2, 3, 4]
    result2: list[int] = scale_element(data2, 2, 10)
    # CPython: [1, 2, 30, 4]
    # Model: [1, 2, 3, 4]
    assert result2 == [1, 2, 30, 4]

    # Test 3: running sum (each element depends on previous modification)
    data3: list[int] = [1, 2, 3, 4]
    result3: list[int] = accumulate_running(data3)
    # CPython: [1, 3, 6, 10]
    # Model: [1, 2, 3, 4] (no modifications happen)
    assert result3 == [1, 3, 6, 10]

    print(result)
    print(result3)


main()
