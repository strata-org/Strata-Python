d = {"a": 1, "b": 2, "c": 3}
del d["b"]
d["b"] = 5
d["a"] = 7
seen = []
def pred(k, v):
    seen.append((k, v))
    if len(seen) == 3:
        raise ValueError(repr(seen))
    return True
# probe: base.Bool = py.allItems($d) ^err {pred2}
# python: contract_rules_ref.allItems_ref(d, pred)
# expect: agree
