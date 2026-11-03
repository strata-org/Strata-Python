# Test: object.__init__'s excess-argument errors, which test the class's tp_new
class A:
    def __new__(cls, *a):
        return object.__new__(cls)
class B(A):
    __new__ = object.__new__
b = B()
try:
    r = object.__init__(b, 1)
    print("ok", r)
except TypeError as e:
    print("TypeError", e.args[0])
class P:
    pass
try:
    object.__init__(P(), 1)
    print("ok")
except TypeError as e:
    print("TypeError", e.args[0])
