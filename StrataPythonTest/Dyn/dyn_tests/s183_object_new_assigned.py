# Test: object.__new__ assigned over a class's own __new__, whose tp_new stays slot_tp_new in CPython
class A:
    def __new__(cls, *a):
        return object.__new__(cls)
    def __init__(self, x):
        self.x = x
A.__new__ = object.__new__
try:
    print("ok", A(2).x)
except TypeError as e:
    print("TypeError", e.args[0])
