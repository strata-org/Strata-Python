d = {"a": 0, "b": 2}
def pred(k, v):
    return v
# probe: base.Bool = py.anyItems($d) ^err {pred2}
# python: contract_rules_ref.anyItems_ref(d, pred)
# expect: agree
