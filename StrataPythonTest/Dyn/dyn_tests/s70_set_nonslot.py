# Test: writing an attribute that is not a slot, on an instance without __dict__, raises AttributeError
class A:
    __slots__ = ("x",)
a = A()
a.q = 1
