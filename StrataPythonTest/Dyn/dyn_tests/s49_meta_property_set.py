# Test: a write and a read of a class attribute through a property with a setter on the metaclass
class M(type):
    @property
    def x(cls):
        return 1
    @x.setter
    def x(cls, v):
        print("setter", v)
class C(metaclass=M):
    pass
C.x = 5
print(C.x)
