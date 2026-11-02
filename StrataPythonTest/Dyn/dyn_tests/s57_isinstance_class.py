# Test: isinstance falls back to the object's __class__, here a property that returns another class
class A:
    pass
class B:
    @property
    def __class__(self):
        return A
print(isinstance(B(), A))
