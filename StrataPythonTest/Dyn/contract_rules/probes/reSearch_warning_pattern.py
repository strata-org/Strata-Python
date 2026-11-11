s = "a"
# probe: base.Bool = py.reSearch("[[a]", $s) ^err
# python: contract_rules_ref.reSearch_ref('[[a]', s)
# expect: gap py.reSearch: a pattern outside the modelled subset of re
