# Test: a write of __doc__ goes to the instance dict of a staticmethod, and is read-only on an int
def f():
    pass
sm = staticmethod(f)
sm.__doc__ = "d"
print(sm.__doc__)
(1).__doc__ = "x"
