# Test: a classmethod and a staticmethod made by __new__ alone, whose callable is unset
class C:
    m = classmethod.__new__(classmethod)
    s = staticmethod.__new__(staticmethod)
try:
    C.m
    print("got m")
except RuntimeError as e:
    print("RT", e.args[0])
try:
    x = C.s
    print("got s", x is None)
except RuntimeError as e:
    print("RT", e.args[0])
