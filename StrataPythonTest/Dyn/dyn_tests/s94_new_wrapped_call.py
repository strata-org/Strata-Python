# Test: a class call runs its own __new__ and __init__, and C.__new__ is not the staticmethod in C.__dict__
class C:
    def __new__(cls, x):
        o = object.__new__(cls)
        o.x = x
        return o
    def __init__(self, x):
        self.y = x + 1
c = C(1)
print(c.x, c.y, C.__new__ is C.__dict__["__new__"])
