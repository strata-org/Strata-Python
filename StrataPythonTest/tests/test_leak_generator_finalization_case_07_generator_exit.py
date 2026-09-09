"""Case 7 (generator finalization): Catching GeneratorExit changes close."""

import gc
import sys


def swallower():
    try:
        yield 1
    except BaseException:
        yield 99


explicit = swallower()
next(explicit)
try:
    explicit.close()
except RuntimeError as error:
    EXPLICIT_RESULT = type(error).__name__
else:
    EXPLICIT_RESULT = "no exception"

# Finish the generator after the failed close so it cannot report again later.
try:
    next(explicit)
except StopIteration:
    pass

UNRAISABLE = []
old_hook = sys.unraisablehook
sys.unraisablehook = lambda report: UNRAISABLE.append(
    type(report.exc_value).__name__
)
try:
    finalized = swallower()
    next(finalized)
    del finalized
    gc.collect()
finally:
    sys.unraisablehook = old_hook

RESULT = EXPLICIT_RESULT, tuple(UNRAISABLE)


if __name__ == "__main__":
    print(repr(RESULT))
