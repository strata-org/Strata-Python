# Test: object.__eq__ called with a keyword raises CPython's TypeError
o = object()
o.__eq__(o, k=1)
