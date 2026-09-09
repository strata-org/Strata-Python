# `raise` must produce exception tag AND terminate — two effects: create
# exception value + make subsequent code unreachable (like return)
"""
`raise ValueError("msg")` must produce an `exception(ValueError("msg"))`
value in the model. Finding 014 identified that raise is silently dropped.

If raise is dropped:
1. Code after raise executes (should be unreachable)
2. No exception value is produced
3. Enclosing except handler is never triggered

The correct translation: `raise E(msg)` produces an exception value
AND makes subsequent code unreachable (like return — finding 165).

Uses ONLY confirmed-accepted constructs: raise, try/except, ValueError.
"""


def explicit_raise() -> int:
    try:
        raise ValueError("test error")
        return 0  # unreachable
    except ValueError:
        return 1


def conditional_raise(x: int) -> int:
    try:
        if x < 0:
            raise ValueError("negative")
        return x * 2
    except ValueError:
        return -1


def raise_stops_execution() -> int:
    """Code after raise must not execute."""
    result: int = 0
    try:
        result = 1
        raise ValueError("stop")
        result = 999  # must NOT execute
    except ValueError:
        pass
    return result  # 1, not 999


def raise_in_function() -> int:
    """Raise in called function propagates to caller."""
    def validate(n: int) -> int:
        if n <= 0:
            raise ValueError("must be positive")
        return n

    try:
        x: int = validate(-5)
        return x  # unreachable
    except ValueError:
        return 0


def reraise_different() -> int:
    """Catch one exception, raise another."""
    try:
        try:
            raise ValueError("original")
        except ValueError:
            raise RuntimeError("wrapped")
    except RuntimeError:
        return 42


def main() -> None:
    assert explicit_raise() == 1
    assert conditional_raise(-5) == -1
    assert conditional_raise(5) == 10
    assert raise_stops_execution() == 1
    assert raise_in_function() == 0
    assert reraise_different() == 42

    print(explicit_raise(), conditional_raise(-5),
          raise_stops_execution())


main()
