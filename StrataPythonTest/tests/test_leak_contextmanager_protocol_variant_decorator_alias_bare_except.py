"""A decorator alias and bare except still suppress body StopIteration."""

from contextlib import contextmanager as manager_factory


@manager_factory
def manager():
    try:
        yield
    except:
        pass


SUPPRESSED = True
try:
    with manager():
        raise StopIteration("from body")
except StopIteration:
    SUPPRESSED = False

RESULT = SUPPRESSED


if __name__ == "__main__":
    print(repr(RESULT))
