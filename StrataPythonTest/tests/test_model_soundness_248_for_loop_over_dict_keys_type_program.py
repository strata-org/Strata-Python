# `for k in d` loop variable type — k must have key type (str); `d[k]` inside
# loop needs key-validity assumption
"""
`for k in d` iterates over dict KEYS. The loop variable `k` has the
KEY type (str for dict[str, int]). The model must:
1. Iterate over unique keys (finding 188/051)
2. Assign correct type to loop variable (str, not Any)
3. Allow `d[k]` inside the loop (key is valid)

All constructs used: dict[str, int], for, str, int — all IN.
Frontend accepts this.
"""


def sum_values(d: dict[str, int]) -> int:
    """Iterate keys, access values."""
    total: int = 0
    for k in d:
        total = total + d[k]
    return total


def collect_keys(d: dict[str, int]) -> list[str]:
    """Collect all keys into a list."""
    result: list[str] = []
    for k in d:
        result.append(k)
    return result


def filter_by_value(d: dict[str, int], threshold: int) -> dict[str, int]:
    """Keep only entries where value > threshold."""
    result: dict[str, int] = {}
    for k in d:
        if d[k] > threshold:
            result[k] = d[k]
    return result


def key_with_max_value(d: dict[str, int]) -> str:
    """Find key with largest value."""
    best_key: str = ""
    best_val: int = 0
    first: bool = True
    for k in d:
        if first or d[k] > best_val:
            best_key = k
            best_val = d[k]
            first = False
    return best_key


def main() -> None:
    d: dict[str, int] = {"a": 1, "b": 2, "c": 3}

    assert sum_values(d) == 6
    assert len(collect_keys(d)) == 3

    filtered: dict[str, int] = filter_by_value(d, 1)
    assert "a" not in filtered
    assert "b" in filtered
    assert "c" in filtered

    assert key_with_max_value(d) == "c"

    print(sum_values(d), len(collect_keys(d)),
          key_with_max_value(d))


main()
