# Dict construction in loop — final contents unprovable; no inductive
# connection between iterations and dict state
"""
DICT CONSTRUCTION IN LOOP — FINAL CONTENTS UNPROVABLE

CPython: d = {}; for k in keys: d[k] = f(k)
         After loop: d contains ALL keys with correct values.

Model:   Each d[k] = v requires rebinding d (finding 146/238).
         Even with correct rebinding, the solver cannot prove:
         - Which keys are in the final dict
         - What values they map to
         Because there's no inductive connection between loop
         iterations and the dict's final state.

         The solver would need:
         - Loop invariant: "d contains all keys processed so far"
         - Post-condition: "d contains all keys in the input"
         - Axioms connecting set/contains/get across iterations

This is the DICT parallel of finding 363 (for-loop iteration count).
"""


def build_from_keys(keys: list[str], value: int) -> dict[str, int]:
    """Build dict from key list — all keys get same value."""
    d: dict[str, int] = {}
    for k in keys:
        d[k] = value
    return d


def build_indexed(items: list[str]) -> dict[str, int]:
    """Build dict mapping each item to its index."""
    d: dict[str, int] = {}
    i: int = 0
    for item in items:
        d[item] = i
        i += 1
    return d


def count_chars(s: str) -> dict[str, int]:
    """Character frequency counter — the canonical dict-building loop."""
    freq: dict[str, int] = {}
    for ch in s:
        if ch in freq:
            freq[ch] = freq[ch] + 1
        else:
            freq[ch] = 1
    return freq


def merge_dicts(a: dict[str, int], b: dict[str, int], keys_b: list[str]) -> dict[str, int]:
    """Merge b into a — result should contain all keys from both."""
    result: dict[str, int] = {}
    # Copy a's keys (simplified — would need a.keys() iteration)
    for k in keys_b:
        result[k] = b[k]
    return result


def main() -> None:
    # Test 1: build from keys
    keys: list[str] = ["x", "y", "z"]
    d: dict[str, int] = build_from_keys(keys, 0)
    # After loop: d must contain "x", "y", "z" all mapping to 0
    # Model: unprovable without loop invariant + set/contains axioms
    assert "x" in d and "y" in d and "z" in d
    assert d["x"] == 0 and d["y"] == 0 and d["z"] == 0
    assert len(d) == 3

    # Test 2: indexed build
    items: list[str] = ["a", "b", "c"]
    indexed: dict[str, int] = build_indexed(items)
    assert indexed["a"] == 0
    assert indexed["b"] == 1
    assert indexed["c"] == 2

    # Test 3: frequency counter
    freq: dict[str, int] = count_chars("aab")
    assert freq["a"] == 2
    assert freq["b"] == 1
    assert len(freq) == 2

    print("all passed")


main()
