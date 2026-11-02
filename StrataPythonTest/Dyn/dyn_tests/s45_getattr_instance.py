# Test: a read of a missing attribute through a __getattr__ that is a callable object, which gets no self
class K:
    def __call__(self, x, y=None):
        return y is None
class C:
    __getattr__ = K()
print(C().abc)
