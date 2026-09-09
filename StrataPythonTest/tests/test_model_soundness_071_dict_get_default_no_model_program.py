# `dict.get(key, default)` has no model — no `DictStrAny_get_default` for safe
# access with fallback
"""
`dict.get(key, default)` returns the value for key if present, otherwise
returns the default value (or None if no default). This is distinct from
`d[key]` which raises KeyError on missing keys. The model's DictStrAny
likely has no `get` method — only `DictStrAny_get` which may have a
precondition that the key exists (or returns Hole for missing keys).
"""


def lookup_or_default(d: dict[str, int], key: str) -> int:
    return d.get(key, 0)


def count_occurrences(words: list[str]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for w in words:
        counts[w] = counts.get(w, 0) + 1
    return counts


def merge_defaults(base: dict[str, int], overrides: dict[str, int], keys: list[str]) -> dict[str, int]:
    result: dict[str, int] = {}
    for k in keys:
        result[k] = overrides.get(k, base.get(k, 0))
    return result


def main() -> None:
    d: dict[str, int] = {"a": 1, "b": 2, "c": 3}

    # Key exists: returns value
    assert lookup_or_default(d, "a") == 1

    # Key missing: returns default
    assert lookup_or_default(d, "z") == 0

    # Count occurrences using .get()
    words: list[str] = ["hello", "world", "hello", "foo", "world", "hello"]
    counts: dict[str, int] = count_occurrences(words)
    assert counts["hello"] == 3
    assert counts["world"] == 2
    assert counts["foo"] == 1

    # Merge with defaults
    base: dict[str, int] = {"x": 10, "y": 20}
    over: dict[str, int] = {"y": 99, "z": 50}
    merged: dict[str, int] = merge_defaults(base, over, ["x", "y", "z"])
    assert merged["x"] == 10   # from base
    assert merged["y"] == 99   # overridden
    assert merged["z"] == 50   # from overrides

    print(counts["hello"], counts["world"], merged["y"])


main()
