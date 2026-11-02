# Test: a deletion of a name that the class has, on an instance without __dict__, is read-only
class A:
    __slots__ = ("x",)
    z = 1
a = A()
del a.z
