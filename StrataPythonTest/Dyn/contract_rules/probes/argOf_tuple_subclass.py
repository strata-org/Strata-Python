class T(tuple):
    pass
args = T((1, 2))
kwargs = {}
d = 0
# probe: py.Value = py.argOf($args, $kwargs, 0, "a", $d)
# python: contract_rules_ref.argOf_ref(args, kwargs, 0, "a", d)
# expect: agree
