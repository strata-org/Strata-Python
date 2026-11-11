args = (1,)
kwargs = {"c": 5, "z": 6}
d = 1
def f(a, b=0, *, c=1, **kw):
    return (a, b, c, kw)
# probe: py.Value = py.argOf($args, $kwargs, -1, "c", $d)
# python: f(*args, **kwargs)[2]
# expect: agree
