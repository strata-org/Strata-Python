# Test: calls of a function object with positional and keyword arguments, and * and ** arguments
def f(a, b=2, *rest, c=3, **kw):
    return (a, b, rest, c, kw)

r1 = f(1)
r2 = f(1, 5, 6, 7, c=8, d=9)
xs = [10, 20]
r3 = f(*xs)
r4 = f(*(1, 2, 3))
r5 = f(*"ab")
m = {"b": 4, "e": 5}
r6 = f(1, **m)
r7 = f(1, **m, c=0)
r8 = f(*{"k": 1})
