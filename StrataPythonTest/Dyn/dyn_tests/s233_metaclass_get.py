# Test: a class stored as an attribute, whose metaclass defines __get__, is a descriptor
class M(type):
    def __get__(cls, obj, owner=None):
        return 42
class D(metaclass=M):
    pass
class C:
    x = D
r = C().x
