# Test: object.__getattribute__ of a super object
class A:
    def f(self):
        return 1
class B(A):
    pass
s = super(B, B())
r = object.__getattribute__(s, 'f')
