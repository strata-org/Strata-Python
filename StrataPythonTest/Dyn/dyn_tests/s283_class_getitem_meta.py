# Test: a __class_getitem__ that the metaclass defines
class M(type):
    def __class_getitem__(cls, k):
        return "meta"
class C(metaclass=M):
    pass
r = C[1]
