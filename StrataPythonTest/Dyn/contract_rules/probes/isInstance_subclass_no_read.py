class B:
    pass
class A(B):
    @property
    def __class__(self):
        raise KeyError("read")
a = A()
C = B
# probe: base.Bool = py.isInstance($a, $C) ^err
# python: isinstance(a, C)
# expect: agree
