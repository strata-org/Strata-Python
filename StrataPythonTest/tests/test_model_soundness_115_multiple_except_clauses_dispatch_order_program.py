# Multiple `except` clauses — must try in order, first match wins, unmatched
# propagates; model may pick wrong handler
"""
Multiple `except` clauses are tried in ORDER. The first matching clause
handles the exception; subsequent clauses are skipped. If no clause
matches, the exception propagates.

The model must try clauses sequentially and stop at the first match.
If it tries all clauses or picks the wrong one, behavior diverges.
"""


def handle_multiple(x: int) -> str:
    try:
        if x == 0:
            raise ValueError("zero")
        if x < 0:
            raise KeyError("negative")
        return "ok"
    except ValueError:
        return "value_error"
    except KeyError:
        return "key_error"


def first_match_wins(x: int) -> str:
    """If exception matches multiple (via inheritance), first wins."""
    try:
        if x < 0:
            raise ValueError("neg")
        return "ok"
    except ValueError:
        return "caught_value"
    except RuntimeError:
        return "caught_runtime"


def no_match_propagates(x: int) -> str:
    """If no clause matches, exception propagates."""
    try:
        if x < 0:
            raise RuntimeError("oops")
        return "ok"
    except ValueError:
        return "caught_value"
    except KeyError:
        return "caught_key"
    # RuntimeError not caught — propagates


def main() -> None:
    # Dispatch to correct handler
    assert handle_multiple(1) == "ok"
    assert handle_multiple(0) == "value_error"
    assert handle_multiple(-1) == "key_error"

    # First matching clause wins
    assert first_match_wins(5) == "ok"
    assert first_match_wins(-1) == "caught_value"

    # No match: propagates
    assert no_match_propagates(5) == "ok"
    raised: bool = False
    try:
        no_match_propagates(-1)
    except RuntimeError:
        raised = True
    assert raised == True

    print(handle_multiple(0), handle_multiple(-1), raised)


main()
