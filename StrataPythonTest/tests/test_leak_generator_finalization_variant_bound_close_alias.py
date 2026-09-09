"""Calling a bound close alias has the same GeneratorExit behavior."""


def generator():
    try:
        yield 1
    except GeneratorExit:
        yield 2


iterator = generator()
next(iterator)
finish = iterator.close
try:
    finish()
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
