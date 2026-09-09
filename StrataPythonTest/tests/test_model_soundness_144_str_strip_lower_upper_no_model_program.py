# `str.strip()`/`str.lower()`/`str.upper()` — IN allowlist but no model;
# results are Hole
"""
`str.strip()` removes leading/trailing whitespace.
`str.lower()` returns lowercase copy.
`str.upper()` returns uppercase copy.
All are IN the allowlist but have no Laurel model — results are Hole.
"""


def clean_input(s: str) -> str:
    return s.strip()


def normalize(s: str) -> str:
    return s.lower()


def shout(s: str) -> str:
    return s.upper()


def clean_and_lower(s: str) -> str:
    return s.strip().lower()


def is_yes(s: str) -> bool:
    cleaned: str = s.strip().lower()
    return cleaned == "yes" or cleaned == "y"


def main() -> None:
    # strip
    assert clean_input("  hello  ") == "hello"
    assert clean_input("no_spaces") == "no_spaces"
    assert clean_input("  ") == ""

    # lower
    assert normalize("Hello World") == "hello world"
    assert normalize("UPPER") == "upper"
    assert normalize("already") == "already"

    # upper
    assert shout("hello") == "HELLO"

    # chained
    assert clean_and_lower("  Hello  ") == "hello"

    # practical: yes/no check
    assert is_yes("  YES  ") == True
    assert is_yes("y") == True
    assert is_yes("no") == False

    print(clean_input("  hi  "), normalize("ABC"), shout("lo"))


main()
