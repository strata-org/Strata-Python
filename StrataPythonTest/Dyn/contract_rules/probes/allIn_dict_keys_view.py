d = {"a": 1}
xs = d.keys()
def pred(x):
    return x
# probe: base.Bool = py.allIn($xs) ^err {pred}
# python: contract_rules_ref.allIn_ref(xs, pred)
# expect: agree
