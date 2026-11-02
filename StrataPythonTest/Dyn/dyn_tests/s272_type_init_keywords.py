# Test: type.__init__ with one argument and a keyword raises CPython's TypeError
class M(type):
    def __new__(mcls, *a, **k):
        if a[0] == 'C':
            return type.__new__(mcls, *a)
        return C
class C(metaclass=M):
    pass
r = M('X', k=1)
