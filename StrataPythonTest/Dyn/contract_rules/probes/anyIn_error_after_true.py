xs = [1, "boom"]
def pred(x):
    if x == "boom":
        raise ValueError(x)
    return x
# probe: base.Bool = py.anyIn($xs) ^err {pred}
# python: contract_rules_ref.anyIn_ref(xs, pred)
# expect: agree
