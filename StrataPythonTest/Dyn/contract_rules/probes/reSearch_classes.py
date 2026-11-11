s = "x = 42 _y"
# probe: base.Bool = py.reSearch("\\w\\s=\\s\\d+\\s\\w", $s) ^err
# python: contract_rules_ref.reSearch_ref('\\w\\s=\\s\\d+\\s\\w', s)
# expect: agree
