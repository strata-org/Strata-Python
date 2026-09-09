# `in` operator right-tag dispatch — `str in str` (substring), `str in list`
# (element), `str in dict` (key) need three algorithms
"""
`in` OPERATOR DISPATCH: string-in-string vs key-in-dict vs element-in-list.

The `in` operator has THREE different semantics depending on the RIGHT operand:
  - `x in lst` → element membership (finding 145 covers bool/int coercion)
  - `k in d`   → key membership (finding 095 covers keys-not-values)
  - `sub in s` → SUBSTRING containment (finding 046 covers this)

The model must dispatch `PIn(left, right)` based on the TAG of the RIGHT
operand. But there's a subtle interaction: when the right operand is a
`from_str` and the left is also `from_str`, the semantics is SUBSTRING
search, not character membership.

The critical gap: if the translator uses a SINGLE `PIn` implementation
that dispatches only on the right operand's tag, it may use the WRONG
algorithm. Specifically:

  "ab" in "abc"  → True (substring)
  "ab" in ["abc", "ab", "x"]  → True (element equality)

Both have `from_str` on the left. The dispatch MUST check the RIGHT tag:
  - right is from_str → substring (SMT str.contains)
  - right is from_ListAny → element equality (List_contains)
  - right is from_DictStrAny → key lookup (DictStrAny_contains)

If the model has a single `contains` function without right-tag dispatch,
it will use the wrong semantics for at least one case.
"""


def substring_check(needle: str, haystack: str) -> bool:
    """String `in` string = substring containment."""
    return needle in haystack


def element_in_list(x: str, lst: list[str]) -> bool:
    """String `in` list = element equality."""
    return x in lst


def key_in_dict(k: str, d: dict[str, int]) -> bool:
    """String `in` dict = key membership."""
    return k in d


def critical_distinction() -> bool:
    """
    Same left operand, different right operand types.
    "ab" in "xaby" → True (substring)
    "ab" in ["xaby"] → False (not equal to "xaby")
    """
    s: str = "ab"
    as_substring: bool = s in "xaby"      # True: "ab" is substring
    as_element: bool = s in ["xaby"]       # False: "ab" != "xaby"
    return as_substring and not as_element


def int_in_list_vs_range(n: int) -> bool:
    """int `in` list = element check."""
    return n in [1, 2, 3, 4, 5]


def combined_checks(word: str, text: str, words: list[str],
                    index: dict[str, int]) -> list[bool]:
    """All three `in` semantics in one function."""
    results: list[bool] = [False, False, False]
    results[0] = word in text       # substring
    results[1] = word in words      # element
    results[2] = word in index      # key
    return results


def main() -> None:
    # Substring containment
    assert substring_check("ell", "hello") == True
    assert substring_check("xyz", "hello") == False
    assert substring_check("", "hello") == True  # empty is always substring

    # Element in list
    assert element_in_list("hello", ["hello", "world"]) == True
    assert element_in_list("ell", ["hello", "world"]) == False  # NOT substring!

    # Key in dict
    assert key_in_dict("a", {"a": 1, "b": 2}) == True
    assert key_in_dict("c", {"a": 1, "b": 2}) == False

    # Critical: same left, different right semantics
    assert critical_distinction() == True

    # Combined — same word, three different `in` semantics
    results: list[bool] = combined_checks(
        "he", "hello", ["hello", "he"], {"he": 1}
    )
    assert results[0] == True   # "he" in "hello" → substring → True
    assert results[1] == True   # "he" in ["hello", "he"] → element → True
    assert results[2] == True   # "he" in {"he": 1} → key → True

    # Now with a word that's a substring but not an element
    results2: list[bool] = combined_checks(
        "ell", "hello", ["hello", "world"], {"hello": 1}
    )
    assert results2[0] == True   # "ell" in "hello" → True (substring)
    assert results2[1] == False  # "ell" in ["hello","world"] → False (no match)
    assert results2[2] == False  # "ell" in {"hello":1} → False (no key)

    print(critical_distinction(), results[0], results2[1])


main()
