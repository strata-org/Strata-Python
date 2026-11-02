# Test: object.__setattr__ called with a keyword raises CPython's TypeError
class C:
    pass
object.__setattr__(C(), "x", 1, k=2)
