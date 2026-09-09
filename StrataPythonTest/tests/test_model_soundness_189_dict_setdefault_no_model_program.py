# `dict.setdefault(key, default)` — conditional set + return; desugars to
# contains-check + conditional set + get
"""
`dict.setdefault(key, default)` returns d[key] if key exists,
otherwise sets d[key] = default and returns default.

It's equivalent to:
    if key not in d:
        d[key] = default
    return d[key]

But as a single atomic operation. Under pure dict semantics, it must:
1. Check if key exists
2. If not, rebind dict with new key-value pair
3. Return the value (existing or default)

This is another dual-return operation (like list.pop — finding 181):
it returns a value AND potentially modifies the dict.

Uses ONLY confirmed-accepted constructs: dict, str, int, function def.
"""


def setdefault_existing() -> int:
    d: dict[str, int] = {"a": 1, "b": 2}
    val: int = d.setdefault("a", 99)
    # "a" exists → returns 1, dict unchanged
    return val  # 1


def setdefault_missing() -> int:
    d: dict[str, int] = {"a": 1}
    val: int = d.setdefault("b", 42)
    # "b" missing → sets d["b"]=42, returns 42
    return val  # 42


def setdefault_modifies_dict() -> int:
    d: dict[str, int] = {"x": 10}
    d.setdefault("y", 20)
    # d now has "y"
    return d["y"]  # 20


def setdefault_doesnt_overwrite() -> int:
    d: dict[str, int] = {"k": 100}
    d.setdefault("k", 999)
    # "k" already exists → NOT overwritten
    return d["k"]  # 100


def counting_pattern() -> dict[str, int]:
    """Common pattern: initialize missing keys to 0."""
    words: list[str] = ["a", "b", "a", "c", "b", "a"]
    counts: dict[str, int] = {}
    for w in words:
        counts.setdefault(w, 0)
        counts[w] = counts[w] + 1
    return counts


def main() -> None:
    assert setdefault_existing() == 1
    assert setdefault_missing() == 42
    assert setdefault_modifies_dict() == 20
    assert setdefault_doesnt_overwrite() == 100

    counts: dict[str, int] = counting_pattern()
    assert counts["a"] == 3
    assert counts["b"] == 2
    assert counts["c"] == 1

    print(setdefault_existing(), setdefault_missing(),
          counts["a"])


main()
