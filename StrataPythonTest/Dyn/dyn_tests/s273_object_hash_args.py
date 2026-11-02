# Test: object.__hash__ called with an argument raises CPython's TypeError
class C:
    pass
o = C()
r = o.__hash__(1)
