# Test: a class call whose metaclass's __getattribute__ is object's
class M(type):
    __getattribute__ = object.__getattribute__
class C(metaclass=M):
    def __new__(cls):
        return object.__new__(cls)
x = C()
