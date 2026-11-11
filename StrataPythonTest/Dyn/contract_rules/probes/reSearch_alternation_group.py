s = "xxcatdog"
# probe: base.Bool = py.reSearch("(?:cat|dog)(?P<n>dog)", $s) ^err
# python: contract_rules_ref.reSearch_ref('(?:cat|dog)(?P<n>dog)', s)
# expect: agree
