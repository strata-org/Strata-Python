# Test: super(C, None), an unbound super object
class C:
    pass
s = super(C, None)
r = type(s).__name__
