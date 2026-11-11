class M(type):
    @property
    def __mro__(cls):
        return (cls, int, object)
class C(metaclass=M):
    pass
x = C()
I = int
# probe: base.Bool = py.typeIsSubclass($x, $I) ^err
# python: contract_rules_ref.typeIsSubclass_ref(x, I)
# expect: agree
