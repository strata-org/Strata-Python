class B:
    def __bool__(self):
        raise ValueError("bool")
xs = [1]
def pred(x):
    return B()
# probe: base.Bool = py.allIn($xs) ^err {pred}
# python: contract_rules_ref.allIn_ref(xs, pred)
# expect: agree
