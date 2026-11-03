# Test: the cut of __context__ cycles of three, and of a tail that ends in a cycle
c = TypeError("c")
x = KeyError("x")
h = ValueError("h")
h.__context__ = x
x.__context__ = c
try:
    try:
        raise h
    except ValueError:
        raise c
except TypeError as t:
    print(t is c, c.__context__ is h, h.__context__ is x, x.__context__ is None)
a = ValueError("a"); b = KeyError("b"); d = IndexError("d")
a.__context__ = b; b.__context__ = d; d.__context__ = a
try:
    try:
        raise a
    except ValueError:
        raise TypeError("c")
except TypeError as c:
    print(c.__context__ is a, a.__context__ is b, b.__context__ is d, d.__context__ is a)
h = ValueError("h"); a = KeyError("a"); b = IndexError("b")
h.__context__ = a; a.__context__ = b; b.__context__ = a
try:
    try:
        raise h
    except ValueError:
        raise TypeError("c")
except TypeError as c:
    print(c.__context__ is h, h.__context__ is a, a.__context__ is b, b.__context__ is a)
c = TypeError("c")
h = ValueError("h")
h.__context__ = c
try:
    try:
        raise h
    except ValueError:
        raise c
except TypeError as t:
    print(c.__context__ is h, h.__context__ is None)
es = [ValueError(0), ValueError(1), ValueError(2), ValueError(3), ValueError(4)]
i = 0
while i < 4:
    es[i].__context__ = es[i + 1]
    i += 1
es[4].__context__ = es[1]
c = TypeError("c")
try:
    try:
        raise es[0]
    except ValueError:
        raise c
except TypeError as t:
    print(t.__context__ is es[0], es[4].__context__ is es[1], es[3].__context__ is es[4])
