x = 1
cs = (int, 5)
# probe: base.Bool = py.typeIsSubclass($x, $cs) ^err
# python: contract_rules_ref.typeIsSubclass_ref(x, cs)
# expect: agree
