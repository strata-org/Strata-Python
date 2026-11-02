# Test: object.__setattr__ on a class raises CPython's TypeError (its hackcheck)
class C:
    pass
object.__setattr__(C, "x", 1)
