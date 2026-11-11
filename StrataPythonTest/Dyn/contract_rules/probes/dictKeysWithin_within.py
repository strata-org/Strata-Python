d = {"a": 1}
# probe: base.Bool = py.dictKeysWithin($d, "a", "b")
# python: contract_rules_ref.dictKeysWithin_ref(d, ["a", "b"])
# expect: agree
