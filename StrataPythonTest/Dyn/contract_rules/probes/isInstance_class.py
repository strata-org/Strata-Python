class C:
    pass
class D(C):
    pass
x = D()
# probe: base.Bool = py.isInstance($x, $C) ^err
# python: isinstance(x, C)
# expect: agree
