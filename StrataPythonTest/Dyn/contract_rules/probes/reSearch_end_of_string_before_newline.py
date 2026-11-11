s = "ab\n"
# probe: base.Bool = py.reSearch("ab\\Z", $s) ^err
# python: contract_rules_ref.reSearch_ref('ab\\Z', s)
# expect: agree
