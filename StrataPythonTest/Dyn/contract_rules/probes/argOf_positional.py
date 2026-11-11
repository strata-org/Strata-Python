args = (1, 2)
kwargs = {"c": 3, "d": 4}
d = None
def f(a, b, *, c, **kw):
    return b
# probe: py.Value = py.argOf($args, $kwargs, 1, "b", $d)
# python: f(*args, **kwargs)
# expect: agree
