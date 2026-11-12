d = {"a": 1, "b": 2}
def pred(k, v):
    raise KeyError(k)
# probe: base.Bool = py.allItems($d) ^err {pred2}
# python: contract_rules_ref.allItems_ref(d, pred)
# expect: agree
