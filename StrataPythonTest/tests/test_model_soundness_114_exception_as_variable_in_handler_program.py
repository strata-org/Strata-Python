# `except ValueError as e` — exception must be bound to variable `e` in
# handler; model may not extract Error value
"""
`except ValueError as e:` binds the exception object to variable `e`.
The handler can access `e` to get the error message or other info.
In the exception-as-value model, `e` must be bound to the Error value
extracted from the exception constructor.
"""


def get_error_message(s: str) -> str:
    try:
        n: int = int(s)
        return str(n)
    except ValueError as e:
        # e is the ValueError instance; str(e) gives the message
        return "error: " + str(e)


def classify_error(s: str, d: dict[str, int]) -> str:
    try:
        n: int = int(s)
        return str(d[str(n)])
    except ValueError as e:
        return "parse_error"
    except KeyError as e:
        return "missing_key"


def reraise_with_context(s: str) -> int:
    """Catch, inspect, and re-raise."""
    try:
        return int(s)
    except ValueError as e:
        # Can inspect e before re-raising
        if "invalid" in str(e):
            raise ValueError("bad input: " + s)
        raise  # re-raise original


def main() -> None:
    # Access exception in handler
    msg: str = get_error_message("abc")
    assert "error:" in msg or "invalid" in msg

    # Normal case
    assert get_error_message("42") == "42"

    # Classify by exception type
    d: dict[str, int] = {"1": 10, "2": 20}
    assert classify_error("1", d) == "10"
    assert classify_error("abc", d) == "parse_error"
    assert classify_error("9", d) == "missing_key"

    # Re-raise
    raised: bool = False
    try:
        reraise_with_context("xyz")
    except ValueError:
        raised = True
    assert raised == True

    print(msg, classify_error("abc", d), raised)


main()
