class M(type):
    def __instancecheck__(cls, v):
        return True
class C(metaclass=M):
    pass
x = 1
# probe: base.Bool = py.isInstance($x, $C) ^err
# python: isinstance(x, C)
# expect: agree
