args = (1, 2)
kwargs = {"c": 3, "d": 4}
d = None
def f(a, b, *, c, **kw):
    pass
# probe: base.Bool = py.bindsTo($args, $kwargs, 2, true, "a", "b", "c")
# python: contract_rules_ref.binds(f, args, kwargs)
# expect: agree
