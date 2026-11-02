# Test: a classmethod that wraps a property, read on the class
class C:
    @classmethod
    @property
    def x(cls):
        return 42
print(C.x == 42)
