class B(bytes):
    pass
s = B(b"ab")
# probe: base.Bool = py.reSearch("a", $s) ^err
# python: contract_rules_ref.reSearch_ref('a', s)
# expect: agree
