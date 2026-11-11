d = {"a": 1}
# probe: base.Bool = py.dictKeysWithin($d)
# python: contract_rules_ref.dictKeysWithin_ref(d, [])
# expect: agree
