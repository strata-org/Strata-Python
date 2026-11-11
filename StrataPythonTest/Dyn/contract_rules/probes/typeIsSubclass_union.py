x = 1
u = int | str
# probe: base.Bool = py.typeIsSubclass($x, $u) ^err
# python: contract_rules_ref.typeIsSubclass_ref(x, u)
# expect: gap built-in method type.__or__ is not modelled yet
