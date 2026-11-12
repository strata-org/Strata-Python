class D(dict):
    def items(self):
        return [("z", 0)]
d = D(a=1)
def pred(k, v):
    return v
# probe: base.Bool = py.anyItems($d) ^err {pred2}
# python: contract_rules_ref.anyItems_ref(d, pred)
# expect: agree
