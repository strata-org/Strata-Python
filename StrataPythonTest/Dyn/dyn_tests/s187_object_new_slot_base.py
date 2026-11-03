# Test: object.__new__ in a class body over a base's own __new__, which keeps slot_tp_new, raises on excess arguments
class A:
    def __new__(cls, *a):
        return object.__new__(cls)
class B(A):
    __new__ = object.__new__
    def __init__(self, x):
        self.x = x
try:
    print("ok", B(1).x)
except TypeError as e:
    print("TypeError", e.args[0])
