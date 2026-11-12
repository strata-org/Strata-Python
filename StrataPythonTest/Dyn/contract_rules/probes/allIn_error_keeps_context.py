xs = [1]
h = KeyError("h")
def pred(x):
    try:
        raise IndexError("i")
    except IndexError:
        raise ValueError("v")
# probe: base.Bool = py.allIn($xs) ^err {pred}
# handling: h
# python: contract_rules_ref.allIn_ref(xs, pred)
# expect: agree
