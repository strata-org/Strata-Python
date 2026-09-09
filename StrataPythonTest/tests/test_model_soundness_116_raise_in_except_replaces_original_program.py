# `raise` in except handler — replaces original exception with new one; model
# must not re-propagate the original
"""
If an exception handler itself raises a new exception, the original
exception is replaced. The new exception propagates; the original is
lost (in CPython it becomes __context__ but that's not in the subset).

The model must handle: exception caught → handler raises new exception
→ new exception propagates (original does NOT continue propagating).
"""


def wrap_error(s: str) -> int:
    """Catch ValueError, raise RuntimeError instead."""
    try:
        return int(s)
    except ValueError:
        raise RuntimeError("parse failed: " + s)


def handler_may_raise(x: int) -> int:
    """Handler itself can raise."""
    try:
        if x < 0:
            raise ValueError("negative")
        return x
    except ValueError:
        if x < -100:
            raise RuntimeError("too negative")
        return 0


def nested_exception_replacement() -> str:
    """Outer try catches the NEW exception from inner handler."""
    try:
        wrap_error("abc")
    except RuntimeError:
        return "caught_runtime"
    except ValueError:
        return "caught_value"  # should NOT reach here
    return "no_error"


def main() -> None:
    # Normal case: no exception
    assert wrap_error("42") == 42

    # ValueError caught, RuntimeError raised instead
    raised_runtime: bool = False
    try:
        wrap_error("abc")
    except RuntimeError:
        raised_runtime = True
    except ValueError:
        raised_runtime = False  # should NOT catch ValueError
    assert raised_runtime == True

    # Handler conditionally raises
    assert handler_may_raise(5) == 5
    assert handler_may_raise(-1) == 0  # caught, returns 0

    raised2: bool = False
    try:
        handler_may_raise(-200)
    except RuntimeError:
        raised2 = True
    assert raised2 == True

    # Nested: outer catches the replacement exception
    assert nested_exception_replacement() == "caught_runtime"

    print(raised_runtime, raised2, nested_exception_replacement())


main()
