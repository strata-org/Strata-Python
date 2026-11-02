# Test: a call of an instance through a __call__ that is a callable object, which gets no self
class K:
    def __call__(self, x, y=None):
        return y is None
class C:
    __call__ = K()
print(C()(1))
