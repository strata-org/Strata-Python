args = ()
kwargs = {}
def f():
    pass
# probe: base.Bool = py.bindsTo($args, $kwargs, 0, false)
# python: contract_rules_ref.binds(f, args, kwargs)
# expect: agree
