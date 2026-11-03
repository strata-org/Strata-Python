# Test: OSError.__new__ leaves the arguments to __init__ when the class's tp_init isn't OSError's
class C(ValueError, OSError):
    pass


c = OSError.__new__(C, 2, "x")
print(type(c).__name__, c.errno, c.args == ())


class D(OSError):
    def __init__(self, *a):
        pass


d = D(2, "x")
print(d.errno, d.args == ())
