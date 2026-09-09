# Dict key overwrite grows assoc-list unboundedly — `DictStrAny_set` prepends
# without removing old entry; root cause of 032/041/051
"""
Dict key assignment (`d[k] = v`) in the model prepends a new entry to
the DictStrAny association list. The old entry for the same key remains
(shadowed). This means:
1. Memory grows unboundedly with repeated overwrites (finding 032 covers len)
2. `DictStrAny_keys` or iteration may yield duplicate keys
3. Equality comparison sees different internal structure for semantically
   equal dicts (finding 041 covers this)

This finding focuses on a NEW consequence: after N overwrites of the
same key, the DictStrAny has N+1 entries. Operations that traverse the
full list (keys(), values(), items(), iteration) have O(N) cost per
overwrite instead of O(1), and may expose shadowed entries.
"""


def count_updates(key: str, n: int) -> dict[str, int]:
    """Overwrite the same key n times."""
    d: dict[str, int] = {}
    i: int = 0
    while i < n:
        d[key] = i
        i = i + 1
    # CPython: d has 1 entry {"key": n-1}
    # Model: DictStrAny has n entries, all for "key", only first is visible
    return d


def overwrite_and_check(d: dict[str, int]) -> int:
    """Overwrite a key and verify dict properties."""
    d["x"] = 1
    d["x"] = 2
    d["x"] = 3
    # CPython: d["x"] == 3, len(d) counts "x" once
    # Model: DictStrAny has 3 entries for "x" (plus original contents)
    return len(d)


def build_frequency_table(words: list[str]) -> dict[str, int]:
    """Classic frequency counter — overwrites keys repeatedly."""
    counts: dict[str, int] = {}
    for w in words:
        if w in counts:
            counts[w] = counts[w] + 1  # overwrite existing key
        else:
            counts[w] = 1
    return counts


def main() -> None:
    # Repeated overwrite: dict still has 1 key
    d1: dict[str, int] = count_updates("x", 100)
    assert d1["x"] == 99
    assert len(d1) == 1  # Model: len might be 100

    # Overwrite and check length
    d2: dict[str, int] = {"a": 10, "b": 20}
    n: int = overwrite_and_check(d2)
    # CPython: d2 = {"a": 10, "b": 20, "x": 3}, len = 3
    assert n == 3  # Model: might count shadowed entries

    # Frequency table: many overwrites
    words: list[str] = ["the", "cat", "sat", "on", "the", "mat", "the"]
    freq: dict[str, int] = build_frequency_table(words)
    assert freq["the"] == 3
    assert freq["cat"] == 1
    assert len(freq) == 5  # 5 unique words

    print(d1["x"], n, freq["the"], len(freq))


main()
