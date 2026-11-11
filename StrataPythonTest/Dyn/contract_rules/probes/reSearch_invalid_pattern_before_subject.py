s = 5
# probe: base.Bool = py.reSearch("(", $s) ^err
# python: contract_rules_ref.reSearch_ref('(', s)
# expect: gap py.reSearch: a pattern outside the modelled subset of re
