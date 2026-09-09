"""A bare except catches GeneratorExit injected by close()."""


def generator():
    try:
        yield 1
    except:
        yield 2


iterator = generator()
next(iterator)
try:
    iterator.close()
except RuntimeError as error:
    RESULT = type(error).__name__, str(error)
else:
    RESULT = "no exception", ""

try:
    next(iterator)
except StopIteration:
    pass


if __name__ == "__main__":
    print(repr(RESULT))
