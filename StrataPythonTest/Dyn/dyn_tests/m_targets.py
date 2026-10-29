# Assignment to attributes and subscripts, in CPython's order: the right-hand side first,
# then the object, then the key.  `x op= e` evaluates the object and the key once.  An
# annotated target with no value evaluates its object and key, and assigns nothing.
o.a = v
o[k] = v
o[a:b] = v
o[a:b:c] = v
o[a:b, c] = v
x = o.a = o[k] = v
o.a += v
o[k] += v
o[a:b] += v
o[a:b:c] += v
o.a.b = v
o[i][j] = v
o.a: int = v
o[k]: int = v
o.a: int
o[k]: int
o[a:b]: int

def f(p):
    p.a = 1
    p[0] += 1
