d = {"a": 1, 2: 3}
# probe: base.Bool = py.dictKeysWithin($d, "a")
# python: contract_rules_ref.dictKeysWithin_ref(d, ["a"])
# expect: agree
