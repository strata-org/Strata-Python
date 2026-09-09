# AUGMENTED ASSIGN ON DICT SUBSCRIPT WITH MISSING KEY — KeyError NOT RAISED
"""
AUGMENTED ASSIGN ON DICT SUBSCRIPT WITH MISSING KEY — KeyError NOT RAISED

The subset allows:
  - dict subscript access d[k] (IN)
  - Augmented assignment d[k] += v (IN — finding 336 covers translation)
  - Exceptions from missing keys (IN — finding 288 covers d[k] on missing key)

The NOVEL gap: `d[k] += 1` when `k` is NOT in `d` raises KeyError in
CPython (because the READ of d[k] fails before the write). But the model
either:
  (a) Returns Hole for the read (no KeyError) — computation continues
      with Hole, producing garbage
  (b) Treats the augmented assign as a pure write (skips the read) —
      no error, d[k] becomes 1 instead of raising

This is DISTINCT from finding 336 which covers the TRANSLATION MECHANICS
(4-step read-modify-write-rebind). This finding covers the ERROR PATH:
when the initial read FAILS, the model must produce an exception, not
silently continue.

CPython: d = {}; d["x"] += 1 → KeyError: 'x'
Model:   d = {}; d["x"] += 1 → either Hole (no error) or d["x"]=1 (wrong)

DISTINCT FROM:
  - Finding 336 (augmented assign translation) — covers mechanics, not error
  - Finding 288 (missing key access) — covers plain d[k], not d[k] += v
  - Finding 084 (dict missing key no KeyError) — covers plain read, not
    augmented assign which has BOTH read AND write semantics
"""


def increment_missing_key() -> int:
    """d[k] += 1 on missing key must raise KeyError."""
    d: dict[str, int] = {}
    d["x"] += 1  # KeyError! "x" not in d
    # CPython: raises KeyError("x")
    # Model: either Hole or d["x"] becomes 1 (no error)
    return d["x"]


def increment_after_guard(d: dict[str, int], key: str) -> int:
    """Safe pattern: check before augmented assign."""
    if key in d:
        d[key] += 1  # safe — key exists
    else:
        d[key] = 1   # initialize
    return d[key]


def accumulate_missing(keys: list[str]) -> dict[str, int]:
    """Common bug: forgetting to initialize before +=."""
    counts: dict[str, int] = {}
    for key in keys:
        counts[key] += 1  # KeyError on first occurrence of each key!
    # CPython: KeyError on first iteration (unless key already in counts)
    # Model: silently produces garbage or Hole
    return counts


def safe_accumulate(keys: list[str]) -> dict[str, int]:
    """Correct pattern for comparison."""
    counts: dict[str, int] = {}
    for key in keys:
        if key in counts:
            counts[key] = counts[key] + 1
        else:
            counts[key] = 1
    return counts


def multiply_missing() -> int:
    """d[k] *= 2 on missing key — same issue."""
    d: dict[str, int] = {"a": 5}
    d["b"] *= 2  # KeyError! "b" not in d
    return d["b"]


def main() -> None:
    # This should raise KeyError
    try:
        increment_missing_key()
        assert False, "Should have raised KeyError"
    except KeyError:
        pass

    # Safe pattern works
    d: dict[str, int] = {"x": 5}
    assert increment_after_guard(d, "x") == 6
    assert increment_after_guard(d, "y") == 1

    # Bug pattern raises
    try:
        accumulate_missing(["a", "b", "a"])
        assert False, "Should have raised KeyError"
    except KeyError:
        pass

    # Correct pattern works
    assert safe_accumulate(["a", "b", "a"]) == {"a": 2, "b": 1}

    print("All passed")


main()
