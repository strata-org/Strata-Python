class S(str):
    def __buffer__(self, f): raise ValueError("no")
s = S("ab")
# probe: base.Bool = py.reSearch("^ab$", $s) ^err
# python: contract_rules_ref.reSearch_ref('^ab$', s)
# expect: agree
