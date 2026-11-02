# Test: an AttributeError from the __get__ of __class_getitem__ means the class has none
class D:
    def __get__(self, obj, owner):
        return owner.nope
class C:
    __class_getitem__ = D()
r = C[1]
