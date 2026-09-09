# **ROOT CAUSE: Exception-as-value no propagation** — no jump to handler, no
# termination after raise; causes 23 findings
"""
ROOT CAUSE: exception(get_error: Error) is a VALUE TAG, not control flow.
PROPERTY: No stack unwinding. No implicit propagation. No jump to handler.

This causes findings:
014, 025, 036, 052, 063, 079, 113, 114, 115, 116, 117, 160, 165,
173, 206, 207, 208, 209, 210, 249, 268, 269, 270.

DEMONSTRATION: Exception value flows into next operation instead of
jumping to handler.
"""


def exception_not_propagated() -> int:
    """After raising op, next statement executes (should be skipped)."""
    try:
        x: int = 10 // 0     # CPython: raises, jumps to except
        y: int = x + 1       # CPython: SKIPPED. Model: executes with Hole/exception
        z: int = y * 2       # CPython: SKIPPED. Model: executes
        return z              # CPython: SKIPPED. Model: returns garbage
    except ZeroDivisionError:
        return -1             # CPython: REACHED. Model: may not reach


def raise_doesnt_terminate() -> int:
    """raise should make subsequent code unreachable."""
    try:
        raise ValueError("stop")
        return 999  # CPython: unreachable. Model: may execute if raise is no-op
    except ValueError:
        return 1


def wrong_handler_catches() -> int:
    """TypeError handler should NOT catch ZeroDivisionError."""
    try:
        try:
            x: int = 1 // 0  # ZeroDivisionError
        except TypeError:     # WRONG handler
            return 1          # should NOT reach
        return 2              # should NOT reach (exception propagates)
    except ZeroDivisionError:
        return 3              # CORRECT handler


def main() -> None:
    assert exception_not_propagated() == -1
    assert raise_doesnt_terminate() == 1
    assert wrong_handler_catches() == 3

    print(exception_not_propagated(), raise_doesnt_terminate(),
          wrong_handler_catches())


main()
