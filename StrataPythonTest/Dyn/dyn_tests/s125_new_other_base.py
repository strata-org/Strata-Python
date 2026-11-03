# Test: a class whose __new__ comes from another built-in base than its tp_new stops with a gap
class C(ValueError, OSError):
    pass
c = C(2, "x")
print(c.errno, type(c).__name__, c.args == (2, "x"))
