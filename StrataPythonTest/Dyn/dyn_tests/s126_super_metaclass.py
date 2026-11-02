# Test: super() with a class whose metaclass is a subclass of type, as an argument and in a metaclass
class M(type):
    def __call__(cls, *a):
        print("meta call")
        return super().__call__(*a)
    def m(cls):
        return super().__repr__ is not None
class C(metaclass=M):
    def __init__(self, x):
        self.x = x
s = super(M, C)
print(type(s) is super, C(3).x, C.m())
class D:
    pass
super(M, D)
