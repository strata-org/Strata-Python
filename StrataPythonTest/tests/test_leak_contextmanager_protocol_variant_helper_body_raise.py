"""A helper-raised body StopIteration is suppressed by contextmanager."""

import contextlib


def fail():
    raise StopIteration("from helper")


@contextlib.contextmanager
def manager():
    try:
        yield
    except StopIteration:
        pass


SUPPRESSED = True
try:
    with manager():
        fail()
except StopIteration:
    SUPPRESSED = False

RESULT = SUPPRESSED


if __name__ == "__main__":
    print(repr(RESULT))
