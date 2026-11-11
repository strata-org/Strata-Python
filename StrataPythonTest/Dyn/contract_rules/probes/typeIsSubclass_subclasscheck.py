class M(type):
    def __subclasscheck__(cls, s):
        return True
class C(metaclass=M):
    pass
x = 1
# probe: base.Bool = py.typeIsSubclass($x, $C) ^err
# python: contract_rules_ref.typeIsSubclass_ref(x, C)
# expect: agree
