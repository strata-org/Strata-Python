class ABCMeta(type):
    __module__ = "abc"
class M2(ABCMeta):
    pass
class C(metaclass=M2):
    pass
x = 1
# probe: base.Bool = py.typeIsSubclass($x, $C) ^err
# python: contract_rules_ref.typeIsSubclass_ref(x, C)
# expect: gap py.typeIsSubclass: a class whose metaclass is abc.ABCMeta is not modelled
