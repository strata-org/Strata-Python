class S(str):
    pass
x = S("w")
# probe: base.Bool = py.strIsOneOf($x, "w")
# python: contract_rules_ref.strIsOneOf_ref(x, ["w"])
# expect: agree
