xs = ["a", "b"]
def pred(x):
    raise ValueError(x)
# probe: base.Bool = py.allIn($xs) ^err {pred}
# python: contract_rules_ref.allIn_ref(xs, pred)
# expect: agree
