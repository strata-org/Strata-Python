# Test: a built-in's __new__ assigned to a class without one, which CPython's slot update ignores
class C(Exception):
    pass
C.__new__ = ValueError.__new__
C(1)
print("reached")
