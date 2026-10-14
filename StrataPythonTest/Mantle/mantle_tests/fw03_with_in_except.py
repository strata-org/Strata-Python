# with inside an except clause: which exception is being handled while __exit__ runs and after
# a with that suppresses, and what a bare raise in the with body raises.
import sys

log = []

def note(x):
    log.append(x)
    return x

class Ctx:
    def __init__(self, suppress):
        self.suppress = suppress
    def __enter__(self):
        return self
    def __exit__(self, t, v, tb):
        note(v)
        note(sys.exc_info()[1])
        return self.suppress

def return_in_clause():
    try:
        raise KeyError("clause")
    except KeyError:
        with Ctx(False):
            return 1  # __exit__ runs before the clause is left: the KeyError is still being handled

def after_suppress():
    try:
        raise KeyError("clause")
    except KeyError:
        with Ctx(True):
            raise ValueError("body")  # __exit__ sees it being handled, and suppresses it
        note(sys.exc_info()[1])  # the KeyError again
        raise IndexError("after")  # its __context__ is the KeyError, not the ValueError

def bare_raise_in_with():
    try:
        raise KeyError("clause")
    except KeyError:
        with Ctx(True):
            raise  # raises the KeyError into the with, whose __exit__ suppresses it
        return note("suppressed")
