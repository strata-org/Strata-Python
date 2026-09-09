# `str.find()` returns index or -1 — no model; maps to SMT-LIB `str.indexof`;
# used in `if s.find(x) >= 0` pattern
"""
`str.find(sub)` returns the lowest index where `sub` is found, or -1
if not found. This is IN the allowlist but has no model. The return
value is used in conditions (`if s.find(x) >= 0`) and as an index.
Maps to SMT-LIB `str.indexof`.
"""


def contains_word(text: str, word: str) -> bool:
    return text.find(word) >= 0


def find_position(text: str, target: str) -> int:
    return text.find(target)


def split_at_char(s: str, sep: str) -> str:
    """Return part before separator, or whole string if not found."""
    pos: int = s.find(sep)
    if pos < 0:
        return s
    # Can't slice, but position is known
    return s  # simplified


def main() -> None:
    # Found: returns index
    assert find_position("hello world", "world") == 6
    assert find_position("hello world", "hello") == 0
    assert find_position("abcabc", "bc") == 1

    # Not found: returns -1
    assert find_position("hello", "xyz") == -1
    assert find_position("", "a") == -1

    # Contains check
    assert contains_word("hello world", "world") == True
    assert contains_word("hello world", "xyz") == False

    # Empty string is always found at position 0
    assert find_position("hello", "") == 0

    print(find_position("hello world", "world"), contains_word("abc", "b"))


main()
