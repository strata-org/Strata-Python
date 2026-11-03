# Test: OSError's construction, its errno subclasses, its fields set or unset, and its str
e = OSError(1, "a", None)
print(e.args == (1, "a", None), e.filename)
e = OSError(1, "a", None, None, "f2")
print(e.args == (1, "a", None, None, "f2"), e.filename, e.filename2)
e = OSError(True, "x")
print(type(e).__name__)
class E(OSError):
    def __init__(self, a, b, c):
        pass
e = E(1, 2, 3)
print(e.args == (), e.errno)
try:
    OSError(2, "x", k=1)
except TypeError as e:
    print(e.args[0])
class E(OSError):
    def __init__(self, *a, **k):
        super().__init__(*a)
e = E(2, "x", "f", k=3)
print(e.args == (2, "x"), e.errno, e.filename, type(e).__name__)
e2 = OSError(2, "x", "f", 7, "g", 8)
print(e2.errno, e2.args == (2, "x", "f", 7, "g", 8))
e = OSError(2, None)
print(e.__str__())
e = OSError(None, "s", "f")
print(e.__str__())
e = OSError(2, "s", "f")
e.errno = None
print(e.__str__())
e = OSError(2, "s")
e.filename = None
print(e.__str__())
e = OSError(2, "s")
e.strerror = None
print(e.__str__())
class NotFound(OSError):
    def __init__(self, path):
        super().__init__(2, "not found", path)
e = NotFound("a.txt")
print(e.errno, e.filename, e.__str__())
