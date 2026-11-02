# Test: object.__lt__ called without an argument raises CPython's TypeError
class C:
    pass
o = C()
r = o.__lt__()
