# Unpacking targets, in CPython's order: the value is unpacked first, then each element is
# assigned in turn, and its target is evaluated only then.  A starred element unpacks with
# unpackEx and receives a list.
a, b = v
[a, b] = v
a, (b, c), d = v
a, *b = v
*a, b, c = v
[a, *b] = v
a, *(b, c) = v
() = v
o.a, (o[k], *r) = v
x = a, b = v

def f(p):
    q, r = p
    return q
