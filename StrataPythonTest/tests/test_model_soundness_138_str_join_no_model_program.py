# `str.join(lst)` — IN allowlist but no model; maps to recursive string
# concatenation with separator
"""
`sep.join(lst)` concatenates list elements with separator between them.
It's IN the allowlist but has no model. The result depends on:
1. The separator string
2. The list elements (must all be strings)
3. len(result) = sum(len(elem)) + len(sep) * (len(lst) - 1)
"""


def join_words(words: list[str]) -> str:
    return " ".join(words)


def join_csv(fields: list[str]) -> str:
    return ",".join(fields)


def join_empty_sep(parts: list[str]) -> str:
    return "".join(parts)


def build_path(segments: list[str]) -> str:
    return "/".join(segments)


def main() -> None:
    # Basic join
    assert join_words(["hello", "world"]) == "hello world"
    assert join_words(["a", "b", "c"]) == "a b c"
    assert join_words(["single"]) == "single"
    assert join_words([]) == ""

    # CSV
    assert join_csv(["name", "age", "city"]) == "name,age,city"

    # Empty separator (concatenation)
    assert join_empty_sep(["a", "b", "c"]) == "abc"

    # Path building
    assert build_path(["home", "user", "docs"]) == "home/user/docs"

    print(join_words(["hello", "world"]), join_csv(["a", "b"]))


main()
