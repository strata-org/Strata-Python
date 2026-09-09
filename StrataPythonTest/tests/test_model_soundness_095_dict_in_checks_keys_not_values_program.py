# `in` on dict checks keys not values — translator must dispatch to
# `DictStrAny_contains` (key check) for dict-typed containers
"""
`key in d` checks whether `key` is a KEY in the dict, not a value.
`value in d` does NOT check if value appears as a dict value — it
checks if `value` is a key. This is a common Python gotcha.

The model's `DictStrAny_contains` must check keys only. If it's
uninterpreted or checks values, the semantics diverge.
"""


def has_key(d: dict[str, int], key: str) -> bool:
    return key in d


def value_not_found_as_key(d: dict[str, int], val: str) -> bool:
    # Even if val appears as a VALUE, `in` checks KEYS
    return val in d


def safe_increment(d: dict[str, int], key: str) -> dict[str, int]:
    if key in d:
        d[key] = d[key] + 1
    else:
        d[key] = 1
    return d


def collect_present(d: dict[str, int], keys: list[str]) -> list[str]:
    result: list[str] = []
    for k in keys:
        if k in d:
            result = result + [k]
    return result


def main() -> None:
    data: dict[str, int] = {"apple": 1, "banana": 2, "cherry": 3}

    # Key exists
    assert has_key(data, "apple") == True
    assert has_key(data, "banana") == True

    # Key doesn't exist
    assert has_key(data, "grape") == False

    # Numeric value is NOT found via `in` (checks keys only)
    # "1" is not a key even though 1 is a value
    assert ("1" in data) == False

    # Safe increment pattern
    counts: dict[str, int] = {}
    counts = safe_increment(counts, "a")
    counts = safe_increment(counts, "b")
    counts = safe_increment(counts, "a")
    assert counts["a"] == 2
    assert counts["b"] == 1

    # Collect present keys
    present: list[str] = collect_present(data, ["apple", "grape", "cherry", "mango"])
    assert present == ["apple", "cherry"]

    print(has_key(data, "apple"), has_key(data, "grape"), present)


main()
