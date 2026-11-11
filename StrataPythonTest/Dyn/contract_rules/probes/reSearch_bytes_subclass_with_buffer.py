class B(bytes):
    def __buffer__(self, f): return memoryview(b"a")
s = B(b"ab")
# probe: base.Bool = py.reSearch("a", $s) ^err
# python: contract_rules_ref.reSearch_ref('a', s)
# expect: gap py.reSearch: a subject whose class defines __buffer__ is not modelled
