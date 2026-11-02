# Test: __mro_entries__ and __prepare__ are read with the attribute protocol
class Weird:
    def __getattr__(self, n):
        print("getattr", n)
        raise AttributeError(n)
w = Weird()
try:
    class X(w):
        pass
except TypeError as e:
    print("TE", e.args[0])
class Holder:
    pass
h = Holder()
class Real:
    pass
h.__mro_entries__ = lambda bases: (Real,)
class X(h):
    pass
print(X.__mro__[1].__name__)
class MM(type):
    def __prepare__(*args):
        print("MM prepare", len(args))
        return {}
class M(metaclass=MM):
    pass
try:
    class X(metaclass=M):
        pass
except TypeError as e:
    print("TE", e.args[0])
