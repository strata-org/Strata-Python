x = "w"
# probe: base.Bool = py.strIsOneOf($x, "r", "w")
# python: contract_rules_ref.strIsOneOf_ref(x, ["r", "w"])
# expect: agree
