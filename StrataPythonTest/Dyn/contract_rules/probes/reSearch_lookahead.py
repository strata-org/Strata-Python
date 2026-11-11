s = "ab"
# probe: base.Bool = py.reSearch("a(?=b)", $s) ^err
# python: contract_rules_ref.reSearch_ref('a(?=b)', s)
# expect: gap py.reSearch: a pattern outside the modelled subset of re
