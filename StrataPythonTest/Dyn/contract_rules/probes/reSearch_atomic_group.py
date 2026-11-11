s = "aaa"
# probe: base.Bool = py.reSearch("(?>a+)a", $s) ^err
# python: contract_rules_ref.reSearch_ref('(?>a+)a', s)
# expect: gap py.reSearch: a pattern outside the modelled subset of re
