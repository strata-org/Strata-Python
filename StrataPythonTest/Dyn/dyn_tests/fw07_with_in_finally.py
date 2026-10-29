# with in a finally body: the with sees the pending exception as the one being handled, and
# suppressing an exception in the with does not cancel it; only leaving the finally body does.
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

def normal_exit():
    try:
        raise KeyError("pending")
    finally:
        with Ctx(False):
            pass  # __exit__ gets None, while the KeyError is being handled

def suppress_in_finally():
    try:
        raise KeyError("pending")
    finally:
        with Ctx(True):
            raise ValueError("body")  # its __context__ is the KeyError; suppressed
        note(sys.exc_info()[1])  # the KeyError again, which then propagates

def reraise_pending():
    try:
        raise KeyError("pending")
    finally:
        with Ctx(True):
            raise  # raises the KeyError into the with, which suppresses it ...
    # ... but the finally body ends normally, so the KeyError still propagates

def return_in_with():
    try:
        raise KeyError("pending")
    finally:
        with Ctx(False):
            return "finally"  # drops the KeyError, after __exit__ ran with it still handled
