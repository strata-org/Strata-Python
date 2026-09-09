# `return` in `finally` overrides `try`/`except` return — deferred return
# semantics needed; or reject as anti-pattern
"""
In Python, a `return` inside a `finally` block OVERRIDES any return value
from the `try` or `except` block. This is a well-known Python gotcha:

    def f():
        try:
            return 1
        finally:
            return 2    # This wins! f() returns 2

Similarly, if `try` raises and `except` returns a value, but `finally`
also returns, the `finally` return wins.

The Laurel model must handle this: `finally` return overrides all other
return paths.

Uses ONLY confirmed-accepted constructs: try/except/finally, return, int.
"""


def finally_overrides_try() -> int:
    try:
        return 1
    finally:
        return 2  # CPython: this overrides, returns 2


def finally_overrides_except() -> int:
    try:
        x: int = int("not_a_number")  # raises ValueError
        return x
    except ValueError:
        return 10
    finally:
        return 99  # CPython: overrides the except's return 10


def finally_no_return_preserves_try() -> int:
    try:
        return 42
    finally:
        # No return here — try's return value is preserved
        x: int = 1 + 1  # side effect only


def finally_no_return_preserves_except() -> int:
    try:
        raise ValueError("oops")
    except ValueError:
        return 7
    finally:
        x: int = 0  # no return — except's return 7 is preserved


def nested_finally() -> int:
    try:
        try:
            return 1
        finally:
            return 2  # inner finally overrides: would return 2
    finally:
        return 3  # outer finally overrides everything: returns 3


def main() -> None:
    # finally return overrides try return
    assert finally_overrides_try() == 2

    # finally return overrides except return
    assert finally_overrides_except() == 99

    # finally without return preserves try's return
    assert finally_no_return_preserves_try() == 42

    # finally without return preserves except's return
    assert finally_no_return_preserves_except() == 7

    # nested finally: outermost wins
    assert nested_finally() == 3

    print(finally_overrides_try(), finally_overrides_except(),
          finally_no_return_preserves_try(), nested_finally())


main()
