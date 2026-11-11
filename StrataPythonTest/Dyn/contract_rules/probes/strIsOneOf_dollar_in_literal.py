x = "a$b"
# probe: base.Bool = py.strIsOneOf($x, "a$b", "$x")
# python: contract_rules_ref.strIsOneOf_ref(x, ["a$b", "$x"])
# expect: agree
