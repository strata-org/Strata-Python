# Test: a classmethod and a staticmethod, each called on the class and on an instance
class C:
    @classmethod
    def f(cls):
        return cls is C
    @staticmethod
    def g(a):
        return a + 1
print(C.f(), C().f(), C.g(1), C().g(2))
