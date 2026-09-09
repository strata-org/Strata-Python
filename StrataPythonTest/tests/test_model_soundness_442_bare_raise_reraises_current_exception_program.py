# Bare `raise` in except handler re-raises current exception — model has no
# "current exception" context; bare raise translates to nothing or Hole
"""
BARE `raise` IN EXCEPT HANDLER RE-RAISES CURRENT EXCEPTION

DIVERGENCE:
  CPython:  `raise` (no argument) in except block re-raises the caught
            exception, propagating it to the next outer handler.
  Model:    `raise` with no argument has no exception value to construct.
            The `exception(...)` tag requires an Error value. Bare `raise`
            either: (a) translates to nothing (silent drop), or
            (b) produces an unbound-variable error in the encoding.

This is IN the subset: `raise` is IN, `try/except` is IN.
The subset says "raise SomeError('message')" but bare `raise` in an
except handler is standard Python and passes mypy --strict.

ROOT CAUSE: The exception-as-value model requires an explicit Error
constructor at every `raise` site. Bare `raise` implicitly references
the "current exception" — a runtime concept with no Laurel equivalent.
"""


def reraise_after_logging() -> int:
    """Catch, log, re-raise — common pattern."""
    try:
        try:
            x: int = 1 // 0
            return x
        except ZeroDivisionError:
            # Log the error, then re-raise
            # CPython: re-raises ZeroDivisionError to outer handler
            # Model: bare `raise` has no Error value → dropped or Hole
            raise
    except ZeroDivisionError:
        return -1


def reraise_conditionally(value: int) -> int:
    """Re-raise only for certain values — common validation pattern."""
    try:
        if value < 0:
            raise ValueError("negative")
        return value * 2
    except ValueError:
        if value == -1:
            # Special case: suppress the error
            return 0
        # All other negatives: re-raise
        # CPython: propagates ValueError("negative")
        # Model: bare `raise` → no propagation
        raise


def reraise_with_cleanup(items: list[int]) -> int:
    """Re-raise after cleanup — resource management pattern."""
    result: int = 0
    try:
        for item in items:
            if item == 0:
                raise ValueError("zero found")
            result = result + 100 // item
    except ValueError:
        result = -999  # cleanup: mark as failed
        # CPython: re-raises, caller sees ValueError
        # Model: bare raise dropped, function returns -999 normally
        raise
    return result


def main() -> None:
    # Test 1: re-raise reaches outer handler
    assert reraise_after_logging() == -1

    # Test 2: conditional re-raise
    assert reraise_conditionally(5) == 10
    assert reraise_conditionally(-1) == 0

    # Test 3: -2 should re-raise
    raised: bool = False
    try:
        reraise_conditionally(-2)
    except ValueError:
        raised = True
    # CPython: raised == True (bare raise propagated)
    # Model: raised == False (bare raise was no-op, function returned... what?)
    assert raised

    # Test 4: re-raise after cleanup
    raised2: bool = False
    try:
        reraise_with_cleanup([1, 2, 0, 3])
    except ValueError:
        raised2 = True
    assert raised2

    print("all passed")


main()
