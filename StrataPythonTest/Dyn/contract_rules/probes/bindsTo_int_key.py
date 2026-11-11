args = ()
kwargs = {1: 2}
def f(**k):
    pass
# probe: base.Bool = py.bindsTo($args, $kwargs, 0, true)
# python: contract_rules_ref.binds(f, args, kwargs)
# expect: agree
