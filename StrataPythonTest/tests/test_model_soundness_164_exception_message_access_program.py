# Exception message access — `str(e)` in handler needs Error to carry message
# string; opaque Error yields Hole
"""
When catching an exception with `except ValueError as e`, the variable
`e` holds the exception instance. Accessing `str(e)` or using `e` in
an f-string retrieves the error message.

The Laurel model uses `exception(get_error: Error)` as a value tag.
But what is `Error`? Can the handler extract the message string from it?
If `Error` is opaque (no fields), then `str(e)` in the handler is Hole.

Additionally, the exception variable `e` is DELETED after the except
block exits (Python 3 semantics — prevents reference cycles with
traceback). The model must not allow access to `e` after the block.

Uses ONLY confirmed-accepted constructs: try/except, ValueError, str, int.
"""


def get_error_message(s: str) -> str:
    try:
        n: int = int(s)
        return ""
    except ValueError as e:
        # str(e) gives the error message
        # In CPython: "invalid literal for int() with base 10: 'abc'"
        msg: str = str(e)
        return msg


def error_message_contains_input(s: str) -> bool:
    try:
        n: int = int(s)
        return False
    except ValueError as e:
        msg: str = str(e)
        # The error message contains the invalid input string
        return s in msg


def classify_error(s: str) -> int:
    """Return 0 for valid, 1 for ValueError, 2 for other."""
    try:
        n: int = int(s)
        return 0
    except ValueError:
        return 1


def reraise_with_context(s: str) -> int:
    try:
        n: int = int(s)
        return n
    except ValueError as e:
        msg: str = str(e)
        raise ValueError("parse failed: " + s)


def main() -> None:
    # Valid input — no exception
    assert get_error_message("42") == ""
    assert classify_error("42") == 0

    # Invalid input — exception caught
    msg: str = get_error_message("abc")
    assert len(msg) > 0  # message is non-empty

    # Error message contains the input
    assert error_message_contains_input("xyz") == True

    # Classify
    assert classify_error("abc") == 1

    # Reraise
    caught: bool = False
    try:
        reraise_with_context("bad")
    except ValueError:
        caught = True
    assert caught == True

    print(classify_error("42"), classify_error("abc"), len(msg) > 0)


main()
