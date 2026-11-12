xs = "ab"
h = KeyError("h")
def pred(x):
    return x
# probe: base.Bool = py.allIn($xs) ^err {pred}
# handling: h
# python: contract_rules_ref.allIn_ref(xs, pred)
# expect: agree
