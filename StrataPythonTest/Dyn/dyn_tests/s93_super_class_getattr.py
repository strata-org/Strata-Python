# Test: a method call through a super() object stored in a local variable
class A:
    def f(self):
        return 1
class B(A):
    def g(self):
        s = super()
        return s.f() + 1
print(B().g())
