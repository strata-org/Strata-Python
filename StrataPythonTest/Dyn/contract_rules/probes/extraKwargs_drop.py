args = (1, 2)
kwargs = {"c": 3, "d": 4}
d = None
# probe: py.Value = py.extraKwargs($kwargs, "c")
# python: (lambda c=None, **k: k)(**kwargs)
# expect: agree
