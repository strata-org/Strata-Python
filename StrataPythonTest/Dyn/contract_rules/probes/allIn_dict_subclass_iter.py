class D(dict):
    def __iter__(self):
        return iter([0])
    def keys(self):
        return [0]
    def __getitem__(self, k):
        return 0
d = D(a=1)
def pred(k):
    return k
# probe: base.Bool = py.allIn($d) ^err {pred}
# python: contract_rules_ref.allIn_ref(d, pred)
# expect: agree
