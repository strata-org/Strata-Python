# `dict[int, V]` is IN but `DictStrAny` only supports string keys — int-keyed
# dicts have no representation
"""
The subset says dict[K, V] for K in {str, int} is IN. But the Any datatype
only has from_DictStrAny (keys are strings). dict[int, V] has no
representation — integer keys cannot be stored in DictStrAny.
"""


def count_occurrences(xs: list[int]) -> dict[int, int]:
    counts: dict[int, int] = {}
    for x in xs:
        if x in counts:
            counts[x] = counts[x] + 1
        else:
            counts[x] = 1
    return counts


def lookup(table: dict[int, str], key: int) -> str:
    if key in table:
        return table[key]
    return "unknown"


def main() -> None:
    # dict with int keys
    counts: dict[int, int] = count_occurrences([1, 2, 1, 3, 2, 1])
    assert counts[1] == 3
    assert counts[2] == 2
    assert counts[3] == 1

    # int-keyed lookup
    table: dict[int, str] = {200: "OK", 404: "Not Found", 500: "Error"}
    assert lookup(table, 200) == "OK"
    assert lookup(table, 999) == "unknown"

    print(counts, lookup(table, 404))


main()
