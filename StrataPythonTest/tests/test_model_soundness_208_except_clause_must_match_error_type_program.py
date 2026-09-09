# Except clause must match error type — Error needs distinct constructors per
# exception class; handler dispatches on constructor tag
"""
`except ValueError` must only catch ValueError, not TypeError or others.
The exception-as-value model must MATCH the exception type in the handler.

Finding 113 identified this. This finding provides concrete cases where
wrong-type exceptions must PROPAGATE past a non-matching handler.

If the model catches ALL exceptions regardless of type:
    try:
        x = 1 // 0  # ZeroDivisionError
    except ValueError:  # should NOT catch ZDE!
        return -1
    # ZDE should propagate UP

Uses ONLY confirmed-accepted constructs: try/except, raise, int.
"""


def wrong_handler_doesnt_catch() -> int:
    """ValueError handler must not catch ZeroDivisionError."""
    try:
        try:
            x: int = 1 // 0  # ZeroDivisionError
        except ValueError:
            return 1  # should NOT be reached
        return 2  # should NOT be reached (exception propagates)
    except ZeroDivisionError:
        return 3  # correct: outer handler catches


def correct_handler_catches() -> int:
    """Matching handler catches the exception."""
    try:
        raise ValueError("test")
    except ValueError:
        return 10  # caught correctly


def first_matching_handler() -> int:
    """Multiple handlers: first match wins."""
    try:
        raise ValueError("x")
    except TypeError:
        return 1  # not this one
    except ValueError:
        return 2  # this one matches
    except RuntimeError:
        return 3  # not reached


def unmatched_propagates() -> int:
    """No matching handler → exception propagates to outer try."""
    try:
        try:
            raise RuntimeError("inner")
        except ValueError:
            return 1  # doesn't match
        except TypeError:
            return 2  # doesn't match
        # RuntimeError propagates out
        return 3  # unreachable
    except RuntimeError:
        return 4  # caught by outer


def main() -> None:
    assert wrong_handler_doesnt_catch() == 3
    assert correct_handler_catches() == 10
    assert first_matching_handler() == 2
    assert unmatched_propagates() == 4

    print(wrong_handler_doesnt_catch(), correct_handler_catches(),
          first_matching_handler())


main()
