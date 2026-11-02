# Test: a class whose __class_getitem__ is None is not subscriptable
class C:
    __class_getitem__ = None
C[1]
