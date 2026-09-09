# Dict `len` after new key vs overwrite — len axiom must be conditional: `+1`
# for new key, `+0` for overwrite
"""
`len(d)` must distinguish between adding a NEW key (len increases by 1)
and OVERWRITING an existing key (len stays the same). The association
list model (finding 082) doesn't distinguish these — both prepend.
Even with McCarthy axioms, the len axiom must be:
  len(set(d, k, v)) == (len(d) + 1) if k not in d else len(d)

Without this conditional, len is either always-incrementing (wrong for
overwrites) or uninterpreted (unprovable).
"""


def add_new_keys() -> int:
    d: dict[str, int] = {}
    d["a"] = 1
    d["b"] = 2
    d["c"] = 3
    return len(d)  # 3 (three new keys)


def overwrite_same_key() -> int:
    d: dict[str, int] = {}
    d["x"] = 1
    d["x"] = 2
    d["x"] = 3
    return len(d)  # 1 (same key overwritten)


def mixed_new_and_overwrite() -> int:
    d: dict[str, int] = {"a": 1, "b": 2}
    d["c"] = 3   # new key: len 2 → 3
    d["a"] = 10  # overwrite: len stays 3
    d["d"] = 4   # new key: len 3 → 4
    d["b"] = 20  # overwrite: len stays 4
    return len(d)  # 4


def build_counter(words: list[str]) -> int:
    """Count unique words. len(d) == number of unique words."""
    d: dict[str, int] = {}
    for w in words:
        if w in d:
            d[w] = d[w] + 1  # overwrite: len unchanged
        else:
            d[w] = 1  # new key: len increases
    return len(d)


def main() -> None:
    # All new keys
    assert add_new_keys() == 3

    # Same key overwritten
    assert overwrite_same_key() == 1

    # Mixed
    assert mixed_new_and_overwrite() == 4

    # Counter: unique word count
    assert build_counter(["a", "b", "a", "c", "b", "a"]) == 3

    # Empty dict
    assert len({}) == 0

    print(add_new_keys(), overwrite_same_key(), mixed_new_and_overwrite())


main()
