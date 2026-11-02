# Test: a method read through super() on the start type itself binds no object
class B:
    pass
f = super(B, B).__init__
f()
