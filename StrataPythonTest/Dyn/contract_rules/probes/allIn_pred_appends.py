xs = [1, 2]
def pred(x):
    xs.append(0)
    return x
# probe: base.Bool = py.allIn($xs) ^err {pred}
# python: contract_rules_ref.allIn_ref(xs, pred)
# expect: agree
