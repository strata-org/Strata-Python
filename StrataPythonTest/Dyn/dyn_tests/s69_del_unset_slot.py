# Test: deleting a slot that is not set raises AttributeError
class A:
    __slots__ = ("x",)
a = A()
del a.x
