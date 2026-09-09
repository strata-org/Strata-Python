# String subscript (`s[i]`) returns `str` — `Any_get!` has no case for
# `from_str` container; no `str_char_at`
"""
In Python, `s[i]` on a string returns a NEW string of length 1 (there
is no separate char type). The model's `Any_get!` likely only handles
`from_ListAny` for subscription. Strings are `from_str` — subscription
on a string requires a separate code path that returns `from_str`.
"""


def first_char(s: str) -> str:
    return s[0]


def last_char(s: str) -> str:
    return s[len(s) - 1]


def char_at(s: str, i: int) -> str:
    return s[i]


def is_digit_string(s: str) -> bool:
    """Check if all characters are digits (0-9)."""
    i: int = 0
    while i < len(s):
        c: str = s[i]
        if c < "0" or c > "9":
            return False
        i = i + 1
    return True


def reverse_string(s: str) -> str:
    result: str = ""
    i: int = len(s) - 1
    while i >= 0:
        result = result + s[i]
        i = i - 1
    return result


def main() -> None:
    word: str = "hello"

    # String indexing returns a string of length 1
    assert first_char(word) == "h"
    assert last_char(word) == "o"
    assert char_at(word, 2) == "l"

    # The result is a str, not a different type
    c: str = word[0]
    assert len(c) == 1
    assert c + "i" == "hi"  # can concatenate (it's a str)

    # Character comparison works (string ordering)
    assert is_digit_string("12345") == True
    assert is_digit_string("123a5") == False

    # Reverse using indexing
    assert reverse_string("abc") == "cba"

    print(first_char(word), reverse_string("abc"))


main()
