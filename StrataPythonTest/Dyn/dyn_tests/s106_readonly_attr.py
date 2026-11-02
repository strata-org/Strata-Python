# Test: a write to a name that the class has, on an instance without __dict__, is read-only
class A:
    __slots__ = ("x",)
    z = 1
a = A()
a.x = 5
print(a.x, a.z)
a.z = 2
