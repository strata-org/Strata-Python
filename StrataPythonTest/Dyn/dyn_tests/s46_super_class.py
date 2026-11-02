# Test: super().__class__ is the super type, not the class of the object
class A:
    pass
class B(A):
    def f(self):
        return super().__class__
print(B().f() is super, B().f() is B)
