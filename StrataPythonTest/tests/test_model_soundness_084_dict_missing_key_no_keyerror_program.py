# Dict missing key access (`d["x"]`) — no KeyError raised; `DictStrAny_get`
# may return Hole instead of exception
"""
Accessing a dict key that doesn't exist (`d["missing"]`) raises KeyError
in CPython. The model's DictStrAny_get either:
1. Has a precondition (key must exist) — correct but may not be enforced
2. Returns Hole for missing keys — unsound (no error reported)
3. Returns exception(KeyError) — correct if exception propagation works

The subset says: "dict indexing preconditions (k in d for dict) are
enforced at check time via assert/assume." But does the model actually
emit these assertions?
"""


def safe_lookup(d: dict[str, int], key: str) -> int:
    if key in d:
        return d[key]  # safe: key existence proven
    return -1


def unsafe_lookup(d: dict[str, int], key: str) -> int:
    # No guard — should raise KeyError if key missing
    return d[key]


def get_or_raise(d: dict[str, int], key: str) -> int:
    if key not in d:
        raise KeyError(key)
    return d[key]


def sum_keys(d: dict[str, int], keys: list[str]) -> int:
    total: int = 0
    for k in keys:
        if k in d:
            total = total + d[k]
    return total


def main() -> None:
    data: dict[str, int] = {"a": 1, "b": 2, "c": 3}

    # Safe lookup with guard
    assert safe_lookup(data, "a") == 1
    assert safe_lookup(data, "z") == -1

    # Unsafe lookup on existing key: works
    assert unsafe_lookup(data, "b") == 2

    # Unsafe lookup on missing key: raises KeyError
    raised: bool = False
    try:
        x: int = unsafe_lookup(data, "missing")
    except KeyError:
        raised = True
    assert raised == True

    # Sum selected keys
    assert sum_keys(data, ["a", "c", "z"]) == 4  # a=1 + c=3, z skipped

    print(safe_lookup(data, "a"), raised)


main()
