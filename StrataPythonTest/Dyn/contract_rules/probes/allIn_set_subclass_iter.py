class S(set):
    def __iter__(self):
        return iter([0])
xs = S([1, 2])
seen = []
def pred(x):
    seen.append(x)
    if len(seen) == 2:
        raise ValueError(repr(seen))
    return x
# probe: base.Bool = py.allIn($xs) ^err {pred}
# python: contract_rules_ref.allIn_ref(xs, pred)
# expect: agree
