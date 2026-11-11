s = "ab\n"
# probe: base.Bool = py.reSearch("ab$", $s) ^err
# python: contract_rules_ref.reSearch_ref('ab$', s)
# expect: agree
