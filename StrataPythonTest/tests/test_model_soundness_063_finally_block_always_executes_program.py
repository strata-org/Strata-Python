# `finally` block always executes — model may skip it on early return or
# exception propagation paths
"""
The `finally` block in Python ALWAYS executes — whether the try block
completes normally, raises an exception, or returns early. In the
exception-as-value model, if `finally` is not explicitly wired into
all exit paths, it may be skipped when a return or exception occurs
in the try block.
"""


def cleanup_on_return(x: int) -> int:
    result: int = 0
    try:
        if x > 0:
            return x * 2  # early return from try
        result = -1
    finally:
        # CPython: ALWAYS executes, even after `return x * 2`
        # The return value is "held" while finally runs
        result = 99  # this assignment happens but doesn't override return

    return result


def cleanup_on_exception(x: int) -> int:
    cleanup_ran: int = 0
    try:
        if x < 0:
            raise ValueError("negative")
        return x
    except ValueError:
        return -1
    finally:
        # CPython: runs after except handler too
        cleanup_ran = 1  # side effect always happens

    # unreachable, but model might think it's reachable
    return cleanup_ran


def finally_modifies_state(xs: list[int]) -> int:
    total: int = 0
    try:
        total = xs[0] + xs[1]  # might raise IndexError
    except IndexError:
        total = -1
    finally:
        total = total + 1000  # always adds 1000

    # CPython: total = (xs[0]+xs[1]) + 1000 or (-1) + 1000
    return total


def main() -> None:
    # Return from try: finally still runs but doesn't override return value
    r1: int = cleanup_on_return(5)
    # CPython: returns 10 (the `return x * 2` value is preserved)
    # finally runs (result=99) but the return value was already captured
    assert r1 == 10

    # Normal path: finally runs, then falls through to `return result`
    r2: int = cleanup_on_return(-1)
    # CPython: result=-1, then finally sets result=99, returns 99
    assert r2 == 99

    # Exception path: finally runs after except handler
    r3: int = cleanup_on_exception(-5)
    # CPython: raises ValueError, caught, returns -1
    # finally runs (cleanup_ran=1) but return already determined
    assert r3 == -1

    # Finally modifies state used in return
    r4: int = finally_modifies_state([10, 20])
    assert r4 == 1030  # 30 + 1000

    r5: int = finally_modifies_state([])
    assert r5 == 999  # -1 + 1000

    print(r1, r2, r3, r4, r5)


main()
