# Test: subscripting a class calls its __class_getitem__ when the metaclass has no __getitem__
class M(type):
    pass
class C(metaclass=M):
    def __class_getitem__(cls, k):
        return k
print(C[3])
