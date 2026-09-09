# `Any_get!` checks `isfrom_int(index)` — `from_bool(True)` fails check, model
# returns TypeError; CPython treats bool as int subclass for indexing
"""
Any_get! checks `isfrom_int(index)` for list subscription. But Python's
bool is a subclass of int, so lst[True] == lst[1] and lst[False] == lst[0]
are valid in CPython. The model rejects from_bool as a list index with
TypeError because from_bool is not from_int.
"""


def get_by_flag(items: list[int], flag: bool) -> int:
    # CPython: bool is subclass of int, so items[True] == items[1]
    # Laurel: Any_get!(from_ListAny(...), from_bool(true))
    #   checks isfrom_int(from_bool(true)) -> false
    #   falls to: exception(TypeError("Invalid subscription type"))
    return items[flag]


def count_if(values: list[int], threshold: int) -> int:
    count: int = 0
    for v in values:
        # (v > threshold) returns bool; using it as index is valid Python
        # This pattern: [0, 1][condition] is equivalent to int(condition)
        count += [0, 1][v > threshold]
    return count


def main() -> None:
    data: list[int] = [10, 20, 30]
    result: int = get_by_flag(data, True)
    print(result)  # CPython: 20, Laurel: exception(TypeError)

    result2: int = get_by_flag(data, False)
    print(result2)  # CPython: 10, Laurel: exception(TypeError)

    total: int = count_if([1, 5, 3, 7, 2], 4)
    print(total)  # CPython: 2, Laurel: exception(TypeError)


main()
