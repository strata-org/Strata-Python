args = (1, 2)
kwargs = {"c": 3, "d": 4}
d = None
def f(a, c, x=0, *, d):
    pass
# probe: base.Bool = py.bindsTo($args, $kwargs, 3, false, "a", "c", "x", "d")
# python: contract_rules_ref.binds(f, args, kwargs)
# expect: agree
