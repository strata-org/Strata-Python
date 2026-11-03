# Test: a lookup that swallows AttributeError (CPython's _PyObject_LookupAttr) also swallows one without name and obj
class E(Exception):
    def __getattr__(self, n):
        raise AttributeError
e = E()
e.add_note("x")
print(e.__notes__[0])
class P:
    def __getattribute__(self, n):
        raise AttributeError
print(isinstance(P(), int))
