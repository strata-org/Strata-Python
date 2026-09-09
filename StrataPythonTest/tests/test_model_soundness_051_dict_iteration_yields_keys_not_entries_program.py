# `for k in d` iterates over dict keys — association list may yield duplicates
# from overwrites or wrong element type
"""
Python's `for x in d` iterates over the KEYS of a dict. The Laurel
encoding uses DictStrAny as an association list. If `for x in d` is
translated as iterating over the association list entries, it may yield
(key, value) pairs or just values, rather than keys alone. Additionally,
if the association list has duplicate keys (from overwrites), iteration
may yield the same key multiple times.
"""


def get_keys(d: dict[str, int]) -> list[str]:
    result: list[str] = []
    for k in d:
        result.append(k)
    return result


def sum_values_via_keys(d: dict[str, int]) -> int:
    total: int = 0
    for k in d:
        total = total + d[k]
    return total


def count_keys(d: dict[str, int]) -> int:
    count: int = 0
    for k in d:
        count = count + 1
    return count


def main() -> None:
    data: dict[str, int] = {"a": 1, "b": 2, "c": 3}

    keys: list[str] = get_keys(data)
    assert len(keys) == 3
    # Keys are strings, not ints
    assert keys[0] == "a"

    total: int = sum_values_via_keys(data)
    assert total == 6  # 1 + 2 + 3

    # After overwrite: dict has 3 unique keys, not 4 entries
    data["b"] = 20
    n: int = count_keys(data)
    assert n == 3  # still 3 keys, not 4

    total2: int = sum_values_via_keys(data)
    assert total2 == 24  # 1 + 20 + 3

    print(keys, total, n, total2)


main()
