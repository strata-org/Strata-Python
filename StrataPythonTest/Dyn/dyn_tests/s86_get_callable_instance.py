# Test: a read through a descriptor whose class's __get__ is a callable object, which gets three arguments
class K:
    def __call__(self, a, b, c=None):
        return c is None
class D:
    __get__ = K()
class C:
    x = D()
print(C().x)
