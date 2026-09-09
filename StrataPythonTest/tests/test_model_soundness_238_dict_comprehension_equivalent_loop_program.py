# Dict construction in loop — `d[k]=v` must rebind d each iteration (finding
# 146); test suite for counting/zipping/conditional patterns
"""
Dict comprehensions are OUT of the subset ("may grow"). But the
EQUIVALENT loop pattern IS in the subset:

    # Comprehension (OUT):
    d = {k: v for k, v in items}

    # Equivalent loop (IN):
    d = {}
    for item in items:
        d[key] = value

This finding verifies that the loop-based dict construction works
correctly under pure dict semantics with rebinding.

The model must handle:
1. Empty dict literal: d = {} → DictStrAny_empty
2. Repeated d[k] = v → rebind d each time (finding 146)
3. Final dict has all keys with correct values

Uses ONLY confirmed-accepted constructs: dict, for, while, str, int.
"""


def build_dict_from_lists(keys: list[str], values: list[int]) -> dict[str, int]:
    """Zip two lists into a dict."""
    d: dict[str, int] = {}
    i: int = 0
    while i < len(keys) and i < len(values):
        d[keys[i]] = values[i]
        i = i + 1
    return d


def count_chars(s: str) -> dict[str, int]:
    """Count character occurrences (simplified: single chars as strings)."""
    counts: dict[str, int] = {}
    i: int = 0
    while i < len(s):
        c: str = s[i]
        if c in counts:
            counts[c] = counts[c] + 1
        else:
            counts[c] = 1
        i = i + 1
    return counts


def invert_dict(d: dict[str, int]) -> dict[str, int]:
    """Swap keys and values (simplified: values become str keys)."""
    result: dict[str, int] = {}
    for k in d.keys():
        result[str(d[k])] = len(k)  # value→key, key_len→value
    return result


def conditional_build(xs: list[int]) -> dict[str, int]:
    """Build dict with conditional inclusion."""
    d: dict[str, int] = {}
    for x in xs:
        if x > 0:
            d["pos"] = d.get("pos", 0) + 1 if "pos" in d else 1
    # Simplified: just count positives
    count: int = 0
    for x in xs:
        if x > 0:
            count = count + 1
    result: dict[str, int] = {}
    result["positive_count"] = count
    return result


def main() -> None:
    d: dict[str, int] = build_dict_from_lists(["a", "b", "c"], [1, 2, 3])
    assert d["a"] == 1
    assert d["b"] == 2
    assert d["c"] == 3
    assert len(d) == 3

    counts: dict[str, int] = count_chars("abracadabra")
    assert counts["a"] == 5
    assert counts["b"] == 2
    assert counts["r"] == 2

    result: dict[str, int] = conditional_build([1, -2, 3, -4, 5])
    assert result["positive_count"] == 3

    print(d["a"], counts["a"], result["positive_count"])


main()
