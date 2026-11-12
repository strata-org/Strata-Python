xs = set()
for i in (3, 1, 2):
    xs.add(i)
seen = []
def pred(x):
    seen.append(x)
    if len(seen) == 3:
        raise ValueError(repr(seen))
    return False
# probe: base.Bool = py.anyIn($xs) ^err {pred}
# python: contract_rules_ref.anyIn_ref(xs, pred)
# expect: agree
