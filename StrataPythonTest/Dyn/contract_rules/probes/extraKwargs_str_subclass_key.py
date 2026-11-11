class S(str):
    pass
kwargs = {S("x"): 1, "y": 2}
# probe: py.Value = py.extraKwargs($kwargs, "x")
# python: contract_rules_ref.extraKwargs_ref(kwargs, ["x"])
# expect: agree
