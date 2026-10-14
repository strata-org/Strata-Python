# with: __enter__ and __exit__ found on the type, and each way out of the body.
import sys

def note(x):
    return x

class Ctx:
    def __init__(self, suppress):
        self.suppress = suppress
    def __enter__(self):
        return self
    def __exit__(self, t, v, tb):
        note(sys.exc_info()[1])  # the body's exception while __exit__ runs, or None
        return self.suppress

def suppressed(f):
    with Ctx(True):
        f()
    return 1  # reached when __exit__ returns a true value

def reraised(f):
    with Ctx(False) as c:
        f()  # what f raises leaves the with
    return c

def loop(xs):
    for x in xs:
        with Ctx(False):
            if x:
                break
            continue  # __exit__(None, None, None) runs before each break and continue
    return 0

def two(a, b):
    with a as x, b as y:  # if b.__enter__ raises, only a.__exit__ runs
        return x, y

def target_fails(m, d):
    with m as d[0]:  # an assignment that raises still runs __exit__
        pass

def shadowed():
    c = Ctx(False)
    c.__enter__ = None  # ignored: __enter__ is looked up on the type
    with c as v:
        return v

def always_raises(m):
    with m:
        raise ValueError  # no other way out: __exit__(None, None, None) is never called

class Body:
    with Ctx(False) as c:
        v = note(c)

with Ctx(False) as top:
    note(top)
