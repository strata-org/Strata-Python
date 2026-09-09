# Nested `try/except` — uncaught exceptions must propagate through multiple
# handler levels to enclosing try
"""
Nested try/except: an inner try/except catches some exceptions, and
uncaught ones propagate to the outer try/except. The exception-as-value
model must correctly propagate through multiple levels of try/except.
"""


def inner_catches(x: int) -> int:
    try:
        if x == 0:
            raise ValueError("zero")
        if x < 0:
            raise KeyError("negative")
        return x
    except ValueError:
        return -1
    # KeyError propagates out


def outer_catches(x: int) -> str:
    try:
        result: int = inner_catches(x)
        return str(result)
    except KeyError:
        return "key_error_caught"


def deeply_nested(x: int) -> str:
    try:
        try:
            try:
                if x == 1:
                    raise ValueError("v")
                if x == 2:
                    raise KeyError("k")
                if x == 3:
                    raise RuntimeError("r")
                return "ok"
            except ValueError:
                return "inner_caught_value"
        except KeyError:
            return "middle_caught_key"
    except RuntimeError:
        return "outer_caught_runtime"


def main() -> None:
    # Inner catches ValueError, KeyError propagates
    assert outer_catches(5) == "5"
    assert outer_catches(0) == "-1"       # ValueError caught by inner
    assert outer_catches(-1) == "key_error_caught"  # KeyError propagates to outer

    # Deeply nested: each level catches its type
    assert deeply_nested(0) == "ok"
    assert deeply_nested(1) == "inner_caught_value"
    assert deeply_nested(2) == "middle_caught_key"
    assert deeply_nested(3) == "outer_caught_runtime"

    print(outer_catches(0), outer_catches(-1), deeply_nested(3))


main()
