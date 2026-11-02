# Test: super() whose object's __class__ raises AttributeError gives the TypeError
class A:
    pass
class B:
    def __getattribute__(self, n):
        if n == "__class__":
            return object.__getattribute__(self, "zzz")
        return object.__getattribute__(self, n)
super(A, B())
