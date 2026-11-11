class T(tuple):
    pass
x = 1
cs = T((int,))
# probe: base.Bool = py.typeIsSubclass($x, $cs) ^err
# python: contract_rules_ref.typeIsSubclass_ref(x, cs)
# expect: gap py.typeIsSubclass: an instance of a subclass of tuple is not modelled
