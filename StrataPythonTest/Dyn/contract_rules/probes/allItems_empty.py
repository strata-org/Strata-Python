d = {}
def pred(k, v):
    return v
# probe: base.Bool = py.allItems($d) ^err {pred2}
# python: contract_rules_ref.allItems_ref(d, pred)
# expect: agree
