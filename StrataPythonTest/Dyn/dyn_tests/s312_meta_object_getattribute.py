# Test: a metaclass that borrows object.__getattribute__ instead of type's
class M(type):
    __getattribute__ = object.__getattribute__
class C(metaclass=M):
    @classmethod
    def k(cls):
        return 1
r = C.k
print(type(r).__name__)
del C
