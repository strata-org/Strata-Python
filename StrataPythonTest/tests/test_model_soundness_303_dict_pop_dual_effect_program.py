# `dict.pop(key)` dual effect — returns value AND removes key; pure function
# model cannot do both in one expression
"""
DICT.POP() HAS DUAL EFFECT: returns value AND removes key.

dict.pop(key) is IN the subset (dict methods are allowed). It has TWO
effects that a pure-function model cannot capture in one operation:
  1. Returns the value associated with key
  2. Removes the key from the dict (mutates in place)

Under value semantics, even if we model pop as a pure function, we need
BOTH the return value AND the modified dict. A single expression `d.pop(k)`
cannot rebind `d` to the shorter dict AND return the popped value.

CPython: d = {"a": 1, "b": 2}; v = d.pop("a"); → v==1, d=={"b": 2}
Model:   d.pop("a") → either returns value (dict unchanged) or
         returns new dict (value lost) — cannot do both.

Same issue as finding 181 (list.pop) but for dicts. Finding 181 identified
the problem for lists; this is the dict-specific instance with its own
semantics (KeyError on missing key, optional default argument).
"""


def pop_existing(d: dict[str, int], key: str) -> int:
    """Pop a key known to exist."""
    return d.pop(key)


def pop_and_check_len(d: dict[str, int], key: str) -> int:
    """Pop reduces length by 1."""
    original_len: int = len(d)
    d.pop(key)
    return len(d)  # Should be original_len - 1


def pop_with_default(d: dict[str, int], key: str) -> int:
    """Pop with default — no KeyError if missing."""
    return d.pop(key, -1)


def drain_dict(d: dict[str, int], keys: list[str]) -> int:
    """Pop multiple keys, sum their values."""
    total: int = 0
    for k in keys:
        if k in d:
            total = total + d.pop(k)
    return total


def pop_then_check_membership(d: dict[str, int], key: str) -> bool:
    """After pop, key should not be in dict."""
    d.pop(key)
    return key in d  # Must be False


def main() -> None:
    # Pop returns the value
    d1: dict[str, int] = {"a": 1, "b": 2, "c": 3}
    v: int = d1.pop("a")
    assert v == 1

    # Dict is modified — key removed
    assert "a" not in d1
    assert len(d1) == 2

    # Pop reduces length
    d2: dict[str, int] = {"x": 10, "y": 20}
    d2.pop("x")
    assert len(d2) == 1

    # Pop with default — missing key returns default
    d3: dict[str, int] = {"a": 1}
    assert d3.pop("b", -1) == -1
    assert len(d3) == 1  # dict unchanged when key missing

    # Pop then check membership
    d4: dict[str, int] = {"k": 99}
    d4.pop("k")
    assert "k" not in d4

    # Drain multiple keys
    d5: dict[str, int] = {"a": 1, "b": 2, "c": 3}
    total: int = drain_dict(d5, ["a", "c"])
    assert total == 4

    print(v, len(d1), d3.pop("b", -1))


main()
