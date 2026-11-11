args = (1, 2)
kwargs = {"c": 3, "d": 4}
d = None
def f(a, b, *, c, **kw):
    return c
# probe: py.Value = py.argOf($args, $kwargs, -1, "c", $d)
# python: f(*args, **kwargs)
# expect: agree
