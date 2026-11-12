d = {"a": 1, "b": 2, "c": 3}
del d["a"]
d["a"] = 4
seen = []
def pred(k):
    seen.append(k)
    if len(seen) == 3:
        raise ValueError(repr(seen))
    return True
# probe: base.Bool = py.allIn($d) ^err {pred}
# python: contract_rules_ref.allIn_ref(d, pred)
# expect: agree
