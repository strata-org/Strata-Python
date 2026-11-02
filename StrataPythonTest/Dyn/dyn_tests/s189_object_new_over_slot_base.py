# Test: object.__new__ over a base's own __new__, which keeps slot_tp_new, raises on excess arguments
class A:
    def __new__(cls, *a):
        return object.__new__(cls)
class B(A):
    __new__ = object.__new__
    def __init__(self, x):
        self.x = x
print(B(1).x)
