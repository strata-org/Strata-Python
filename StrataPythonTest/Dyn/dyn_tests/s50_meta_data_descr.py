# Test: a write and a read of a class attribute through a data descriptor on the metaclass
class D:
    def __get__(self, o, t):
        return 1
    def __set__(self, o, v):
        print("set", v)
class M(type):
    x = D()
class C(metaclass=M):
    pass
C.x = 5
print(C.x)
