s = "aaab"
# probe: base.Bool = py.reSearch("a{2,3}?b", $s) ^err
# python: contract_rules_ref.reSearch_ref('a{2,3}?b', s)
# expect: agree
