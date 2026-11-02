# Test: a __class_getitem__ whose __get__ gives None makes the class not subscriptable
class NoneGet:
    def __get__(self, obj, owner=None):
        return None
class A:
    __class_getitem__ = NoneGet()
r = A[1]
