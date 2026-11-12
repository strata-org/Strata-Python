xs = [0, "boom"]
def pred(x):
    if x == "boom":
        raise ValueError(x)
    return x
# probe: base.Bool = py.allIn($xs) ^err {pred}
# python: contract_rules_ref.allIn_ref(xs, pred)
# expect: agree
