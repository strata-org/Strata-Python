class B:
    def __buffer__(self, flags):
        return memoryview(b"a")
s = B()
# probe: base.Bool = py.reSearch("a", $s) ^err
# python: contract_rules_ref.reSearch_ref('a', s)
# expect: gap py.reSearch: a subject whose class defines __buffer__ is not modelled
