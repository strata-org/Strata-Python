# Test: a slot descriptor of one class, stored in another class and written on its instance, raises TypeError
class A:
    __slots__ = ("x",)
class B:
    pass
B.y = A.x
b = B()
b.y = 5
print(b.y)
