# `"sub" in "string"` — string `in` is substring containment, not element
# membership; model likely has no substring search implementation
"""
Python's `in` operator on strings checks for SUBSTRING containment:
`"ab" in "abc"` is True. This is fundamentally different from `in` on
lists (which checks element membership). The model's PContains likely
dispatches to List_contains for lists and DictStrAny_contains for dicts,
but may have no substring-search implementation for strings — falling
to Hole or using character-level membership instead of substring search.
"""


def has_prefix_manual(text: str, prefix: str) -> bool:
    # `in` on strings is substring containment
    return prefix in text


def find_keyword(text: str) -> str:
    if "error" in text:
        return "found_error"
    if "warning" in text:
        return "found_warning"
    return "clean"


def filter_lines(lines: list[str], keyword: str) -> list[str]:
    result: list[str] = []
    for line in lines:
        if keyword in line:
            result.append(line)
    return result


def main() -> None:
    # Substring containment (multi-char)
    assert "bc" in "abcdef"
    assert "xyz" not in "abcdef"

    # Single char containment (looks like element membership but isn't)
    assert "a" in "abc"
    assert "d" not in "abc"

    # Empty string is always a substring
    assert "" in "anything"
    assert "" in ""

    # Full string is a substring of itself
    assert "hello" in "hello"

    # Keyword search
    r1: str = find_keyword("an error occurred")
    assert r1 == "found_error"

    r2: str = find_keyword("all good")
    assert r2 == "clean"

    # Filter
    lines: list[str] = ["error: bad", "info: ok", "error: worse", "debug: fine"]
    filtered: list[str] = filter_lines(lines, "error")
    assert len(filtered) == 2
    assert filtered[0] == "error: bad"
    assert filtered[1] == "error: worse"

    print(r1, r2, filtered)


main()
