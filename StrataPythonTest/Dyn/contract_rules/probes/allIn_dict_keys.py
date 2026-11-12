xs = {"a": 0, "b": 0}
def pred(k):
    return k
# probe: base.Bool = py.allIn($xs) ^err {pred}
# python: contract_rules_ref.allIn_ref(xs, pred)
# expect: agree
