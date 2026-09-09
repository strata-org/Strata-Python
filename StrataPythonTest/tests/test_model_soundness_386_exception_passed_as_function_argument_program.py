# Exception passed as function argument — `f(g())` where g raises; exception
# flows INTO f instead of propagating BEFORE call
"""
EXCEPTION PASSED AS FUNCTION ARGUMENT — MUST PROPAGATE BEFORE CALL

CPython: f(g()) where g() raises → f() is NEVER CALLED.
         The exception from g() propagates immediately.

Model:   g() returns exception(ValueError(...))
         f(exception(ValueError(...))) → f is CALLED with exception as arg
         Inside f: operations on the exception-valued parameter produce Hole
         f returns some value → caller continues as if nothing happened

         The exception is SILENTLY CONSUMED by being passed as an argument.
         CPython would have propagated it BEFORE the call to f.
"""


def might_raise(x: int) -> int:
    if x < 0:
        raise ValueError("negative")
    return x * 2


def use_value(n: int) -> int:
    """Pure function that uses its argument."""
    return n + 100


def caller_passes_exception() -> int:
    """f(g()) where g raises — f should never execute."""
    result: int = use_value(might_raise(-5))
    # CPython: might_raise(-5) raises → use_value never called
    # Model: use_value(exception(...)) → operates on exception → Hole or wrong
    return result


def multi_arg_first_raises(a: int, b: int) -> int:
    """f(g(), h()) — g raises, h should not even evaluate."""
    return a + b


def caller_multi_arg() -> int:
    """First argument raises — second should not evaluate."""
    result: int = multi_arg_first_raises(might_raise(-1), might_raise(5))
    # CPython: first arg raises → second arg never evaluated → function never called
    # Model: both args evaluated, exception flows into function
    return result


def exception_in_method_arg() -> int:
    """Exception as argument to method call."""
    xs: list[int] = [1, 2, 3]
    xs.append(might_raise(-1))
    # CPython: might_raise raises → append never called → xs unchanged
    # Model: append(exception(...)) → exception stored in list or Hole
    return len(xs)


def main() -> None:
    # Test 1: exception in single arg
    raised: bool = False
    try:
        caller_passes_exception()
    except ValueError:
        raised = True
    assert raised

    # Test 2: exception in first of multiple args
    raised2: bool = False
    try:
        caller_multi_arg()
    except ValueError:
        raised2 = True
    assert raised2

    # Test 3: exception in method arg
    raised3: bool = False
    try:
        exception_in_method_arg()
    except ValueError:
        raised3 = True
    assert raised3

    # Test 4: no exception path works normally
    assert use_value(might_raise(5)) == 110  # 5*2=10, 10+100=110

    print("all passed")


main()
