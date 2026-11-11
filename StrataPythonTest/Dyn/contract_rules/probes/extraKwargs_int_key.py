kwargs = {"x": 1, 2: 3}
# probe: py.Value = py.extraKwargs($kwargs, "x")
# python: contract_rules_ref.extraKwargs_ref(kwargs, ["x"])
# expect: agree
