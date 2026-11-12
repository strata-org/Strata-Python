class T(tuple):
    def __iter__(self):
        return iter([0])
xs = T((1, 2))
def pred(x):
    return x
# probe: base.Bool = py.allIn($xs) ^err {pred}
# python: contract_rules_ref.allIn_ref(xs, pred)
# expect: agree
