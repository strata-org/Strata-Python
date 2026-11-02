# Test: isinstance falls back to the object's __class__, here a descriptor with only __get__
class A:
    pass
class ClassOf:
    def __get__(self, o, t):
        return A
class B:
    __class__ = ClassOf()
print(isinstance(B(), A))
