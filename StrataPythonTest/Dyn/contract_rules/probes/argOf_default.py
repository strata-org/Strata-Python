args = (1, 2)
kwargs = {"c": 3, "d": 4}
d = "default"
def f(a, b, *, c, e="default", **kw):
    return e
# probe: py.Value = py.argOf($args, $kwargs, 5, "e", $d)
# python: f(*args, **kwargs)
# expect: agree
