# Test: a method saved by __init_subclass__ reads __class__ after the class's creation failed
saved = [None]
class Base:
    def __init_subclass__(cls):
        saved[0] = cls.f
        raise ValueError("no")
try:
    class C(Base):
        def f(self):
            return __class__
except ValueError:
    print("failed")
print(saved[0](None) is not None)
