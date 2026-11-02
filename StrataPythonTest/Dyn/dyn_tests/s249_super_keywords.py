# Test: super() called with a keyword raises CPython's TypeError
class C:
    pass
super(C, C(), k=1)
