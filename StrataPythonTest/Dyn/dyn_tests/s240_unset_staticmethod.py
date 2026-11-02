# Test: a staticmethod made by __new__ alone, read from a class
class C:
    pass
C.f = staticmethod.__new__(staticmethod)
r = C.f
