# Test: object.__ne__ called with two arguments raises CPython's TypeError
class C:
    pass
o = C()
r = o.__ne__(o, o)
