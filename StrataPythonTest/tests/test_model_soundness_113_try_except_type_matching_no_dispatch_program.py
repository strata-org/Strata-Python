# `try/except` type matching — model may catch ALL exceptions regardless of
# type; no dispatch on Error constructor
"""
`try/except ValueError` must only catch ValueError, not KeyError or
other exceptions. The exception-as-value model stores the exception
type in the Error value. The `except` clause must CHECK the type and
only execute if it matches. If the model doesn't dispatch on exception
type, ALL exceptions are caught by ANY except clause.
"""


def parse_int(s: str) -> int:
    try:
        return int(s)
    except ValueError:
        return -1


def safe_lookup(d: dict[str, int], key: str) -> int:
    try:
        return d[key]
    except KeyError:
        return 0


def wrong_handler(s: str) -> int:
    """ValueError is raised but KeyError handler should NOT catch it."""
    try:
        return int(s)
    except KeyError:
        # This should NOT execute for ValueError
        return -999


def correct_dispatch(s: str, d: dict[str, int]) -> int:
    """Multiple operations, different exception types."""
    try:
        n: int = int(s)       # may raise ValueError
        return d[str(n)]      # may raise KeyError
    except ValueError:
        return -1             # only catches ValueError
    except KeyError:
        return -2             # only catches KeyError


def main() -> None:
    # ValueError caught by except ValueError
    assert parse_int("42") == 42
    assert parse_int("abc") == -1

    # KeyError caught by except KeyError
    d: dict[str, int] = {"a": 1, "b": 2}
    assert safe_lookup(d, "a") == 1
    assert safe_lookup(d, "z") == 0

    # ValueError NOT caught by except KeyError — propagates
    raised: bool = False
    try:
        result: int = wrong_handler("abc")
    except ValueError:
        raised = True
    assert raised == True

    # Correct dispatch to matching handler
    assert correct_dispatch("5", {"5": 50}) == 50
    assert correct_dispatch("abc", {"5": 50}) == -1   # ValueError
    assert correct_dispatch("5", {"x": 1}) == -2      # KeyError

    print(parse_int("abc"), safe_lookup(d, "z"), correct_dispatch("abc", {}))


main()
