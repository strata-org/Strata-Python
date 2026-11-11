class M(type):
    def __instancecheck__(cls, inst):
        raise KeyError("checked")
class C(metaclass=M):
    pass
x = C()
# probe: base.Bool = py.isInstance($x, $C) ^err
# python: isinstance(x, C)
# expect: agree
