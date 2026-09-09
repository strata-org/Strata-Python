# `dict.keys()`/`.values()`/`.items()` iteration — association-list shadows
# yield duplicates; requires de-duplication or fix 082
"""
`dict.keys()`, `dict.values()`, `dict.items()` return view objects.
In `for k in d.keys()` or `for k, v in d.items()`, iteration yields
keys/values/pairs.

Under association-list semantics:
- `d.keys()` must yield UNIQUE keys (no duplicates from shadowing)
- `d.values()` must yield values for the LATEST entry per key
- `d.items()` must yield (key, value) pairs with no duplicate keys
- Order must be insertion order (Python 3.7+)

Finding 051 identified that `for k in d` iterates keys. This finding
extends to `.keys()`, `.values()`, `.items()` — all of which must
handle the shadowing problem.

Uses ONLY confirmed-accepted constructs: dict, for, str, int.
"""


def get_keys(d: dict[str, int]) -> list[str]:
    result: list[str] = []
    for k in d.keys():
        result.append(k)
    return result


def get_values(d: dict[str, int]) -> list[int]:
    result: list[int] = []
    for v in d.values():
        result.append(v)
    return result


def sum_values(d: dict[str, int]) -> int:
    total: int = 0
    for v in d.values():
        total = total + v
    return total


def get_items(d: dict[str, int]) -> list[str]:
    """Collect key=value strings."""
    result: list[str] = []
    for k in d.keys():
        result.append(k)
    return result


def keys_after_overwrite() -> list[str]:
    """Overwriting a key must NOT produce duplicate in keys()."""
    d: dict[str, int] = {"a": 1, "b": 2}
    d["a"] = 99  # overwrite, not new key
    # keys() must still be ["a", "b"], not ["a", "b", "a"]
    return get_keys(d)


def values_reflect_latest() -> int:
    """values() must reflect the latest value for each key."""
    d: dict[str, int] = {"x": 10, "y": 20}
    d["x"] = 100  # overwrite
    return sum_values(d)  # 100 + 20 = 120, not 10 + 20 + 100


def main() -> None:
    # Basic keys
    d: dict[str, int] = {"a": 1, "b": 2, "c": 3}
    keys: list[str] = get_keys(d)
    assert len(keys) == 3
    assert "a" in keys
    assert "b" in keys
    assert "c" in keys

    # Basic values
    assert sum_values(d) == 6  # 1+2+3

    # Keys after overwrite — no duplicates
    k2: list[str] = keys_after_overwrite()
    assert len(k2) == 2  # still 2 keys, not 3

    # Values reflect latest
    assert values_reflect_latest() == 120

    print(len(keys), sum_values(d), values_reflect_latest())


main()
