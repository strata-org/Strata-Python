s = "abcXYZ"
# probe: base.Bool = py.reSearch("^[a-zA-Z]+$", $s) ^err
# python: contract_rules_ref.reSearch_ref('^[a-zA-Z]+$', s)
# expect: agree
