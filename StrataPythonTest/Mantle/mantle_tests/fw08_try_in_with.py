# try statements in a with body: __exit__ sees how the try statement ended after its except
# clause or finally body changed how its body ended.
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
    with Ctx(False):
        try:
            raise KeyError("body")
        except KeyError:
            return 1  # the clause is left before __exit__ runs: nothing is being handled

def finally_returns():
    with Ctx(False):
        try:
            raise KeyError("body")
        finally:
            return "finally"  # drops the KeyError: __exit__ gets None, and nothing is handled

def finally_raises():
    with Ctx(True):
        try:
            return "body"
        finally:
            raise ValueError("finally")  # drops the return; __exit__ suppresses the ValueError
    return "after"  # so the function returns here
