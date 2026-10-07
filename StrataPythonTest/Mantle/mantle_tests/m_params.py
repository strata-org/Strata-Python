# Every parameter kind, with constant defaults.
def f(a, /, b, c=2, *rest, d, e=-1.5, **kw):
    return a

f(1, 2)
