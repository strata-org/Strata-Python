# Test: object.__setattr__ called on a class raises TypeError
class C:
    pass
object.__setattr__(C, "x", 1)
print(C.x)
