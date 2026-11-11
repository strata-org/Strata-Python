args = (1, 2)
kwargs = {"c": 3, "d": 4}
d = None
def f(a, *, b=0, c, d):
    pass
# probe: base.Bool = py.bindsTo($args, $kwargs, 1, false, "a", "b", "c", "d")
# python: contract_rules_ref.binds(f, args, kwargs)
# expect: agree
