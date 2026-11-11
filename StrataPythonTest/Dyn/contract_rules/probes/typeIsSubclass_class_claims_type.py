class A:
    @property
    def __class__(self):
        return type
c = A()
x = 1
# probe: base.Bool = py.typeIsSubclass($x, $c) ^err
# python: contract_rules_ref.typeIsSubclass_ref(x, c)
# expect: agree
