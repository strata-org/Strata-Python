class H:
    pass
H.v = "^err.0()"
# probe: base.Bool = py.strIsOneOf($H.v, "^err")
# python: contract_rules_ref.strIsOneOf_ref(H.v, ["^err"])
# expect: agree
