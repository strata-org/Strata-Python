# with a, b: each item is evaluated and entered before the next one, and a's __exit__ sees how
# b's __exit__ ended.
log = []

def note(x):
    log.append(x)
    return x

class Ctx:
    def __init__(self, name, suppress, fail):
        note("make " + name)
        self.name = name
        self.suppress = suppress
        self.fail = fail
    def __enter__(self):
        note("enter " + self.name)
        return self.name
    def __exit__(self, t, v, tb):
        note("exit " + self.name)
        note(v)
        if self.fail:
            raise ValueError(self.name)
        return self.suppress

def order():
    # a is made, entered and bound to x before the second item is evaluated, which reads x.
    with Ctx("a", False, False) as x, Ctx(x + "2", False, False) as y:
        note(y)
    return "after"

def chained(a_suppress, b_suppress, b_fail):
    # b's __exit__ runs first.  If it suppresses the KeyError, a's __exit__ gets None.  If it
    # raises, a's gets that ValueError, whose __context__ is the KeyError, and may suppress it.
    with Ctx("a", a_suppress, False), Ctx("b", b_suppress, b_fail):
        raise KeyError("body")
    return "after"
