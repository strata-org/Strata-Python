class S(str):
    pass
d = {S("a"): 1}
# probe: base.Bool = py.dictKeysWithin($d, "a")
# python: contract_rules_ref.dictKeysWithin_ref(d, ["a"])
# expect: agree
