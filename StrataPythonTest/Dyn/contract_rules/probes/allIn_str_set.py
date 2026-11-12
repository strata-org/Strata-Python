xs = {"a", "b"}
def pred(x):
    return x
# probe: base.Bool = py.allIn($xs) ^err {pred}
# python: contract_rules_ref.allIn_ref(xs, pred)
# expect: gap py.allIn: a set whose order the model doesn't know
