# `str.replace()` — no model for string substitution; maps to SMT-LIB
# `str.replace_all`
"""
`str.replace(old, new)` returns a NEW string with all occurrences of
`old` replaced by `new`. The original string is unchanged (strings are
immutable). This is IN the allowlist but has no model.
Maps to SMT-LIB `str.replace_all`.
"""


def sanitize(s: str) -> str:
    return s.replace("<", "").replace(">", "")


def normalize_spaces(s: str) -> str:
    # Replace double spaces with single (one pass only)
    return s.replace("  ", " ")


def replace_extension(filename: str, new_ext: str) -> str:
    return filename.replace(".txt", new_ext)


def main() -> None:
    # Basic replace
    assert "hello world".replace("world", "python") == "hello python"
    assert "aaa".replace("a", "b") == "bbb"

    # Replace not found: returns original
    assert "hello".replace("xyz", "abc") == "hello"

    # Replace empty string (inserts between chars)
    assert "ab".replace("", "-") == "-a-b-"

    # Sanitize
    assert sanitize("<script>alert</script>") == "scriptalert/script"

    # Replace extension
    assert replace_extension("data.txt", ".csv") == "data.csv"

    # Original unchanged (immutable)
    s: str = "hello"
    t: str = s.replace("h", "j")
    assert s == "hello"  # unchanged
    assert t == "jello"

    print(t, sanitize("<b>hi</b>"))


main()
