# `"bc" in "abcd"` substring check — needs SMT-LIB `str.contains`;
# uninterpreted str_contains gives Unknown
"""
STRING IN STRING — SUBSTRING CONTAINMENT CHECK

CPython: "bc" in "abcd" → True (substring check)
         "xy" in "abcd" → False
         "" in "anything" → True (empty string is substring of everything)

Model:   PIn(from_str("bc"), from_str("abcd"))
         → needs str_contains("abcd", "bc") → True
         If uninterpreted: UNPROVABLE
         If mapped to SMT-LIB str.contains: trivially provable

         Finding 046 identified this. This provides the concrete test
         showing the model can't prove basic substring checks.

CPython result: True
Model result: Unknown (str_contains uninterpreted)
"""


def has_substring(haystack: str, needle: str) -> bool:
    """Basic substring check."""
    return needle in haystack


def contains_word(text: str, word: str) -> bool:
    """Check if text contains a word."""
    return word in text


def starts_with_manual(s: str, prefix: str) -> bool:
    """Manual startswith using 'in' — less precise but tests containment."""
    # Note: this is weaker than startswith (checks anywhere, not just start)
    return prefix in s


def filter_containing(texts: list[str], keyword: str) -> list[str]:
    """Filter strings that contain a keyword."""
    result: list[str] = []
    for t in texts:
        if keyword in t:
            result.append(t)
    return result


def main() -> None:
    # Test 1: basic containment
    assert has_substring("hello world", "world")
    assert has_substring("hello world", "lo wo")
    assert not has_substring("hello world", "xyz")

    # Test 2: empty string always contained
    assert has_substring("anything", "")
    assert has_substring("", "")

    # Test 3: full string contained in itself
    assert has_substring("abc", "abc")

    # Test 4: single character
    assert has_substring("hello", "e")
    assert not has_substring("hello", "x")

    # Test 5: filter
    texts: list[str] = ["apple pie", "banana split", "apple sauce"]
    result: list[str] = filter_containing(texts, "apple")
    assert len(result) == 2

    print("all passed")


main()
