# `dict.get(key, default)` — no model; must return value if key exists,
# default otherwise; never raises KeyError
"""
dict.get(key, default) return type — must be V or type(default).

Finding 071 notes dict.get() has no model. This finding specifically
tests the RETURN TYPE issue: dict.get(key, default) returns either:
  - The value associated with key (type V), OR
  - The default value (type of default argument)

In CPython:
  d = {"a": 1, "b": 2}
  d.get("a", 0)    → 1     (found: returns value)
  d.get("z", 0)    → 0     (not found: returns default)
  d.get("z", -1)   → -1    (default can be any value)
  d.get("z")       → None  (no default: returns None)

The model must:
1. Check if key exists in the dict
2. If yes: return the associated value
3. If no: return the default argument (or from_None if no default)

Without this, dict.get() returns Hole, and the common pattern
`d.get(key, default_value)` is unverifiable.

Uses ONLY confirmed-accepted constructs: dict, str, int, if, comparison.
"""


def get_existing(d: dict[str, int], key: str) -> int:
    """dict.get on existing key returns the value."""
    return d.get(key, 0)
    # CPython with d={"a":1}, key="a": 1
    # Model: Hole (no dict.get model)


def get_missing(d: dict[str, int], key: str) -> int:
    """dict.get on missing key returns default."""
    return d.get(key, -1)
    # CPython with d={"a":1}, key="z": -1
    # Model: Hole


def get_vs_subscript(d: dict[str, int], key: str) -> int:
    """dict.get is safe alternative to d[key] (no KeyError)."""
    # d[key] raises KeyError if missing
    # d.get(key, 0) returns 0 if missing — no exception
    return d.get(key, 0)
    # CPython: never raises KeyError
    # Model: Hole (can't prove no exception either)


def count_with_get(words: list[str]) -> dict[str, int]:
    """Common pattern: counting with dict.get."""
    counts: dict[str, int] = {}
    for word in words:
        counts[word] = counts.get(word, 0) + 1
    return counts
    # CPython: {"hello": 2, "world": 1} for ["hello", "world", "hello"]
    # Model: counts.get(word, 0) → Hole; Hole + 1 → Hole; dict never grows


def get_then_compare(d: dict[str, int], key: str, threshold: int) -> bool:
    """Using get result in comparison."""
    val: int = d.get(key, 0)
    return val > threshold
    # CPython: compares actual value or default against threshold
    # Model: Hole > threshold → unknown


def main() -> None:
    d: dict[str, int] = {"a": 1, "b": 2, "c": 3}
    assert get_existing(d, "a") == 1
    assert get_existing(d, "b") == 2
    assert get_missing(d, "z") == -1
    assert get_vs_subscript(d, "a") == 1
    assert get_vs_subscript(d, "z") == 0
    assert get_then_compare(d, "c", 2) == True
    assert get_then_compare(d, "z", 2) == False
