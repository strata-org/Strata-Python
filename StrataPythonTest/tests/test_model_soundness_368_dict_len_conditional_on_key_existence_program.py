# Dict len conditional on key existence — overwrite: len unchanged; new key:
# len+1; assoc-list counts shadows (WRONG value)
"""
DICT LEN CONDITIONAL ON KEY EXISTENCE — NEW KEY vs OVERWRITE

CPython: d = {"x": 1}; d["x"] = 2; len(d) == 1 (overwrite, no growth)
         d = {"x": 1}; d["y"] = 2; len(d) == 2 (new key, grows)

Model:   DictStrAny_set PREPENDS to association list (finding 082).
         DictStrAny_len counts ALL entries including shadows.
         After overwrite: len counts BOTH old and new entry → WRONG.

         Even with a correct len model, the axiom is CONDITIONAL:
         - If k ∈ d: len(set(d, k, v)) == len(d)     (overwrite)
         - If k ∉ d: len(set(d, k, v)) == len(d) + 1 (new key)

         This conditional axiom is HARDER than the list version
         (which is always +1 for append). It requires the solver
         to reason about key presence BEFORE computing length.

Finding 032 identified the wrong-count issue.
Finding 097 identified the conditional axiom need.
This finding provides the CONCRETE program showing both cases.
"""


def overwrite_same_len() -> bool:
    """Overwriting existing key: len unchanged."""
    d: dict[str, int] = {"x": 1, "y": 2}
    d["x"] = 99  # overwrite
    # CPython: len(d) == 2 (still two keys)
    # Model (assoc-list): len == 3 (old "x" shadowed but counted)
    return len(d) == 2


def new_key_grows_len() -> bool:
    """Adding new key: len increases by 1."""
    d: dict[str, int] = {"x": 1}
    d["y"] = 2  # new key
    # CPython: len(d) == 2
    # Model: needs axiom: k ∉ d ⟹ len(set(d,k,v)) == len(d) + 1
    return len(d) == 2


def mixed_operations() -> bool:
    """Mix of new keys and overwrites."""
    d: dict[str, int] = {}
    d["a"] = 1   # new: len 0 → 1
    d["b"] = 2   # new: len 1 → 2
    d["a"] = 10  # overwrite: len stays 2
    d["c"] = 3   # new: len 2 → 3
    d["b"] = 20  # overwrite: len stays 3
    return len(d) == 3


def count_unique_keys(words: list[str]) -> int:
    """Frequency counter — len gives unique key count."""
    freq: dict[str, int] = {}
    for w in words:
        if w in freq:
            freq[w] = freq[w] + 1  # overwrite: len unchanged
        else:
            freq[w] = 1  # new key: len += 1
    return len(freq)


def main() -> None:
    assert overwrite_same_len()
    assert new_key_grows_len()
    assert mixed_operations()

    # Frequency counter: unique words
    words: list[str] = ["a", "b", "a", "c", "b", "a"]
    assert count_unique_keys(words) == 3  # "a", "b", "c"

    print("all passed")


main()
