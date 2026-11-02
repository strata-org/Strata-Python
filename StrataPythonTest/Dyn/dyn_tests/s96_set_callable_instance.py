# Test: a write through a data descriptor whose class's __set__ is a callable object
class K:
    def __call__(self, a, b=None):
        print(b is None)
class D:
    def __get__(self, o, t):
        return 1
    __set__ = K()
class C:
    x = D()
C().x = 5
