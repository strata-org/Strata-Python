# `assert` failure raises AssertionError — model only assumes; `try/except
# AssertionError` handler unreachable
"""
assert failure raises AssertionError — model treats assert as assume only.

Finding 123 notes that `assert` must translate as check + assume. But
there's a deeper issue: when the assertion FAILS, CPython raises
AssertionError. This is a catchable exception:

    try:
        assert x > 0, "must be positive"
    except AssertionError as e:
        print(str(e))  # "must be positive"

If the model translates `assert cond` as just `assume(cond)` (making
subsequent code unreachable when cond is false), then:
1. The AssertionError is never produced as an exception value
2. `try/except AssertionError` handlers are unreachable
3. The message string is lost

The model must produce exception(AssertionError) on the failing path,
not just make it unreachable.

Uses ONLY confirmed-accepted constructs: assert, try/except, str, if.
"""


def assert_simple(x: int) -> int:
    """assert that fails raises AssertionError."""
    assert x > 0
    return x
    # CPython with x=-1: AssertionError
    # Model: assume(x > 0) makes x=-1 path unreachable — no error reported


def assert_with_message(x: int) -> int:
    """assert with message string."""
    assert x > 0, "x must be positive"
    return x
    # CPython with x=-1: AssertionError("x must be positive")
    # Model: message string is lost; just assume(x > 0)


def catch_assertion_error(x: int) -> str:
    """try/except AssertionError — handler must be reachable."""
    try:
        assert x > 0, "negative"
        return "ok"
    except AssertionError:
        return "caught"
    # CPython with x=-1: "caught"
    # Model: assert makes x<=0 unreachable → handler dead code → always "ok"


def assert_in_helper(x: int) -> str:
    """Assert in called function — exception propagates to caller."""
    try:
        validate(x)
        return "valid"
    except AssertionError:
        return "invalid"
    # CPython with x=-1: validate raises AssertionError → "invalid"
    # Model: validate's assert makes path unreachable → always "valid"


def validate(x: int) -> None:
    """Helper that asserts precondition."""
    assert x >= 0, "must be non-negative"


def main() -> None:
    assert assert_simple(5) == 5
    assert assert_with_message(5) == 5

    # These trigger AssertionError:
    assert catch_assertion_error(5) == "ok"
    assert catch_assertion_error(-1) == "caught"

    assert assert_in_helper(5) == "valid"
    assert assert_in_helper(-1) == "invalid"
