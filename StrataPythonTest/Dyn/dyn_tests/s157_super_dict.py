# Test: super().__dict__ finds the __dict__ descriptor in a user base class's namespace
class B:
    pass


class C(B):
    def f(self):
        return super().__dict__


c = C()
c.x = 1
print(c.f())
