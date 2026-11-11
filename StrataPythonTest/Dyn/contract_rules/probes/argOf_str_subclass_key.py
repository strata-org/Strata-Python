class S(str):
    pass
args = ()
kwargs = {S("c"): 3}
d = 0
# probe: py.Value = py.argOf($args, $kwargs, -1, "c", $d)
# python: contract_rules_ref.argOf_ref(args, kwargs, -1, "c", d)
# expect: agree
