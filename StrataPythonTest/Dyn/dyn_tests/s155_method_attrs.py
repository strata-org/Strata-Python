# Test: a bound method's attributes are its function's, after the method type's own
class C:
    def m(self):
        return 1

    @classmethod
    def cm(cls):
        return 2


c = C()
print(c.m.__name__, c.m.__module__)
print(C.cm.__name__)
try:
    c.m.nope
except AttributeError as e:
    print("AttributeError", e.args[0])
print(c.m.__func__ is C.m, c.m.__self__ is c, C.cm.__self__ is C)
