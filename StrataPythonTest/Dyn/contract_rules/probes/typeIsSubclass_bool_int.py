x = True
I = int
# probe: base.Bool = py.typeIsSubclass($x, $I) ^err
# python: contract_rules_ref.typeIsSubclass_ref(x, I)
# expect: agree
