class F(frozenset):
    def __iter__(self):
        return iter([0])
xs = F([5, 3])
seen = []
def pred(x):
    seen.append(x)
    if len(seen) == 2:
        raise ValueError(repr(seen))
    return x
# probe: base.Bool = py.anyIn($xs) ^err {pred}
# python: contract_rules_ref.anyIn_ref(xs, pred)
# expect: agree
