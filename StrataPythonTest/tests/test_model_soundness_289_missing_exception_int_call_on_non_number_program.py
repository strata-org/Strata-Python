# Missing exception: `int("hello")` → ValueError; model returns Hole; must
# produce exception for invalid strings
"""
MISSING EXCEPTION: int("hello") → ValueError in CPython, Hole in model.

CPython: int() on a non-numeric string raises ValueError.
Model: to_int_any(from_str("hello")) → Hole (no error produced)

The model thinks int("hello") MIGHT SUCCEED and return some int.
"""


def parse_int_invalid() -> int:
    return int("hello")  # ValueError!


def parse_int_empty() -> int:
    return int("")  # ValueError!


def parse_int_float_str() -> int:
    return int("3.14")  # ValueError! (not a valid int literal)


def safe_parse(s: str) -> int:
    """Correct pattern: catch ValueError."""
    try:
        return int(s)
    except ValueError:
        return -1


def main() -> None:
    caught1: bool = False
    try:
        parse_int_invalid()
    except ValueError:
        caught1 = True
    assert caught1 == True

    caught2: bool = False
    try:
        parse_int_empty()
    except ValueError:
        caught2 = True
    assert caught2 == True

    caught3: bool = False
    try:
        parse_int_float_str()
    except ValueError:
        caught3 = True
    assert caught3 == True

    # Safe parse works
    assert safe_parse("42") == 42
    assert safe_parse("bad") == -1

    print(caught1, caught2, safe_parse("42"))


main()
