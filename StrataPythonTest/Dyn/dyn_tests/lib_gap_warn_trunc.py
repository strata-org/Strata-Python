# int() delegating to __trunc__ warns, which writes __warningregistry__: a gap.
class A:
    def __trunc__(self):
        return 3


print("before")
x = int(A())
