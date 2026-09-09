"""PEP 479 converts a StopIteration raised by a nested helper call."""


def fail():
    raise StopIteration("from helper")


def generator():
    yield "started"
    fail()


iterator = generator()
FIRST = next(iterator)
try:
    next(iterator)
except RuntimeError as error:
    RESULT = (
        FIRST,
        type(error).__name__,
        type(error.__cause__).__name__,
        error.__suppress_context__,
    )
else:
    RESULT = FIRST, "no exception", None, False


if __name__ == "__main__":
    print(repr(RESULT))
