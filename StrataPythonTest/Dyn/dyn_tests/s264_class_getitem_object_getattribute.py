# Test: a metaclass whose __getattribute__ is object's, and a class that inherits __class_getitem__
class M(type):
    __getattribute__ = object.__getattribute__
class B:
    def __class_getitem__(cls, k):
        return k
class C(B, metaclass=M):
    pass
r = C[1]
