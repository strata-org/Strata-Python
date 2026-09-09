# Association-list shadowing comprehensive breakage — ROOT CAUSE of findings
# 032/041/051/082/096/188; fix: replace-on-set or use SMT Array theory
"""
The ROOT CAUSE of multiple dict findings (032, 041, 051, 082, 096, 188):
DictStrAny_set PREPENDS without removing the old entry, creating shadows.

This finding provides a COMPREHENSIVE test suite showing all the ways
shadowing breaks dict semantics:

1. len() counts shadows (finding 032)
2. equality is order-dependent (finding 041)
3. iteration yields duplicates (finding 051)
4. contains works (accidentally) but for wrong reason
5. get returns correct value (first match) but shadows waste space

The fix for ALL of these is: DictStrAny_set must REPLACE, not shadow.

Uses ONLY confirmed-accepted constructs: dict, str, int, len, in.
"""


def overwrite_preserves_len() -> bool:
    """Overwriting a key must NOT increase len."""
    d: dict[str, int] = {"a": 1, "b": 2}
    d["a"] = 99  # overwrite, not new key
    return len(d) == 2  # must still be 2, not 3


def multiple_overwrites_same_len() -> bool:
    """Multiple overwrites of same key: len stays constant."""
    d: dict[str, int] = {"x": 0}
    d["x"] = 1
    d["x"] = 2
    d["x"] = 3
    return len(d) == 1  # still 1 key


def overwrite_then_count_keys() -> int:
    """Count unique keys after overwrites."""
    d: dict[str, int] = {}
    d["a"] = 1
    d["b"] = 2
    d["a"] = 10  # overwrite
    d["c"] = 3
    d["b"] = 20  # overwrite
    return len(d)  # 3 unique keys: a, b, c


def get_returns_latest() -> int:
    """After overwrite, get must return the latest value."""
    d: dict[str, int] = {"k": 1}
    d["k"] = 2
    d["k"] = 3
    return d["k"]  # 3 (latest)


def contains_after_overwrite() -> bool:
    """Key is still present after overwrite (trivially true)."""
    d: dict[str, int] = {"x": 10}
    d["x"] = 20
    return "x" in d  # True


def equality_order_independent() -> bool:
    """Two dicts with same key-value pairs are equal regardless of
    insertion order."""
    d1: dict[str, int] = {"a": 1, "b": 2}
    d2: dict[str, int] = {"b": 2, "a": 1}
    return d1 == d2  # True in CPython


def main() -> None:
    # Len preserved on overwrite
    assert overwrite_preserves_len() == True

    # Multiple overwrites
    assert multiple_overwrites_same_len() == True

    # Count after mixed adds/overwrites
    assert overwrite_then_count_keys() == 3

    # Get returns latest
    assert get_returns_latest() == 3

    # Contains after overwrite
    assert contains_after_overwrite() == True

    # Equality is order-independent
    assert equality_order_independent() == True

    print(overwrite_preserves_len(), multiple_overwrites_same_len(),
          overwrite_then_count_keys())


main()
