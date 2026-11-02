# Test: super.__init__ with other arguments than the object's own
class C:
    pass
s = super(C, C())
super.__init__(s, 1, 2)
