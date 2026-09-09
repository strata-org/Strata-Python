"""Case 8 (contextmanager): A body StopIteration is suppressed."""

import contextlib


@contextlib.contextmanager
def manager():
    try:
        yield
    except StopIteration:
        pass


SUPPRESSED = True
try:
    with manager():
        raise StopIteration("from with body")
except StopIteration:
    SUPPRESSED = False

RESULT = SUPPRESSED


if __name__ == "__main__":
    print(repr(RESULT))
