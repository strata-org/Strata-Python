# `str.startswith()`/`str.endswith()` — IN allowlist but no model; maps to
# SMT-LIB `str.prefixof`/`str.suffixof`
"""
`str.startswith(prefix)` returns True if the string starts with prefix.
`str.endswith(suffix)` returns True if the string ends with suffix.
Both are IN the subset allowlist but have no Laurel model — results
are Hole. They map directly to SMT-LIB `str.prefixof`/`str.suffixof`.
"""


def has_prefix(s: str, prefix: str) -> bool:
    return s.startswith(prefix)


def has_suffix(s: str, suffix: str) -> bool:
    return s.endswith(suffix)


def classify_path(path: str) -> str:
    if path.startswith("/"):
        if path.endswith(".py"):
            return "absolute python"
        return "absolute other"
    if path.endswith(".py"):
        return "relative python"
    return "relative other"


def strip_prefix(s: str, prefix: str) -> str:
    if s.startswith(prefix):
        # Can't slice (finding 068), return as-is for now
        return s
    return s


def main() -> None:
    assert has_prefix("hello world", "hello") == True
    assert has_prefix("hello world", "world") == False
    assert has_prefix("", "") == True
    assert has_prefix("abc", "") == True

    assert has_suffix("hello world", "world") == True
    assert has_suffix("hello world", "hello") == False
    assert has_suffix("file.py", ".py") == True

    assert classify_path("/home/user/main.py") == "absolute python"
    assert classify_path("/etc/config") == "absolute other"
    assert classify_path("script.py") == "relative python"
    assert classify_path("README.md") == "relative other"

    print(has_prefix("hello", "he"), has_suffix("file.py", ".py"))


main()
