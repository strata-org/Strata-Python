# Test: another exception from the __get__ of __class_getitem__ propagates
class D:
    def __get__(self, obj, owner):
        return {}[1]
class C:
    __class_getitem__ = D()
r = C[1]
