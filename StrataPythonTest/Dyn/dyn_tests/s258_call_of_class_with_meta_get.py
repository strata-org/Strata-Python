# Test: a __call__ that is a class whose metaclass defines __get__
class M(type):
    def __get__(cls, obj, owner=None):
        return lambda: 42
class K(metaclass=M):
    pass
class C:
    __call__ = K
r = C()()
