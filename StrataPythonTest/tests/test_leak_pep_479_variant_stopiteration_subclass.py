"""PEP 479 converts subclasses of StopIteration too."""


class Done(StopIteration):
    pass


def generator():
    if False:
        yield None
    raise Done("subclass")


try:
    next(generator())
except RuntimeError as error:
    RESULT = (
        type(error).__name__,
        type(error.__cause__).__name__,
        type(error.__context__).__name__,
    )
else:
    RESULT = "no exception", None, None


if __name__ == "__main__":
    print(repr(RESULT))
