# `except SomeError as e:` — variable `e` is implicitly deleted after handler
# exits; model keeps it in scope (NameError missed)
"""
In Python 3, the variable bound in `except SomeError as e:` is DELETED
when the except block exits. This is explicit in the language spec:
the `as` target is implicitly `del`'d at the end of the handler.

    try:
        ...
    except ValueError as e:
        msg = str(e)
    # e is UNBOUND here — accessing it raises NameError

The Laurel model likely keeps `e` in scope after the handler (since it
has no implicit-del semantics). This creates two divergences:

1. If code after the handler reads `e`, CPython raises NameError but
   the model provides a value (UNSOUND: model misses a crash).
2. If `e` shadows an outer variable, the outer variable is also deleted
   in CPython (the del applies to the name in the local scope).

Uses ONLY confirmed-accepted constructs: try/except, ValueError, str, int.
"""


def get_error_message(s: str) -> str:
    """Capture exception message inside handler, use after handler."""
    msg: str = ""
    try:
        n: int = int(s)
    except ValueError as e:
        msg = str(e)
    # e is DELETED here in CPython
    # Model likely still has e in scope
    return msg


def exception_variable_shadows_outer(x: int) -> int:
    """The except-as variable shadows and then deletes an outer name."""
    e: int = x  # outer e
    try:
        result: int = 10 // 0
    except ZeroDivisionError as e:  # type: ignore
        pass
    # In CPython: e is DELETED (both the exception AND the outer int)
    # NameError if we try to read e here
    # Model: e might still hold the ZeroDivisionError or the outer int
    return x  # safe — don't read e


def handler_variable_not_accessible_after(values: list[str]) -> list[int]:
    """Parse integers, collecting errors. e is deleted each iteration."""
    results: list[int] = []
    last_error: str = ""
    for s in values:
        try:
            results.append(int(s))
        except ValueError as e:
            last_error = str(e)
        # e is deleted here — each iteration
    return results


def main() -> None:
    # Basic: message captured inside handler
    msg: str = get_error_message("not_a_number")
    assert len(msg) > 0  # got the error message

    msg2: str = get_error_message("42")
    assert msg2 == ""  # no exception, msg stays empty

    # Shadow test: outer e is destroyed
    result: int = exception_variable_shadows_outer(99)
    assert result == 99

    # Loop with handler
    parsed: list[int] = handler_variable_not_accessible_after(["1", "bad", "3"])
    assert len(parsed) == 2
    assert parsed[0] == 1
    assert parsed[1] == 3

    print("All except-as-variable tests pass")


main()
