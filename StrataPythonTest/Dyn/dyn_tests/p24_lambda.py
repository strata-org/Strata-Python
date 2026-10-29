# A lambda is a function scope; its defaults are evaluated in the enclosing scope.
k = 1
add = lambda a, b=k: a + b + k


def f(n):
    return lambda x, *r, y=n, **kw: x + n + y
