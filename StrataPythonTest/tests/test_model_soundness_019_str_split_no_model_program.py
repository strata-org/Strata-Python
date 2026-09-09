# `str.split()` (and other allowlisted string methods) have no Laurel model;
# result is unconstrained Hole
"""
str.split() is explicitly IN the Frontend subset, but like list.append(),
it has no model in the Laurel prelude. The havoc fallback makes the
return value (a list[str]) unconstrained, losing all properties of the
split result (element count, content, relationship to original string).
"""


def count_words(text: str) -> int:
    parts: list[str] = text.split()
    return len(parts)


def first_word(text: str) -> str:
    parts: list[str] = text.split()
    if len(parts) == 0:
        return ""
    return parts[0]


def main() -> None:
    sentence: str = "hello world foo"

    n: int = count_words(sentence)
    # CPython: split() returns ["hello", "world", "foo"], len is 3
    assert n == 3

    w: str = first_word(sentence)
    # CPython: parts[0] is "hello"
    assert w == "hello"

    # Empty string splits to empty list
    empty_count: int = count_words("")
    # CPython: "".split() returns [], len is 0
    assert empty_count == 0

    print(n, w, empty_count)


main()
