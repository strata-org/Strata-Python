class A:
    @property
    def __class__(self):
        raise KeyError("read")
a = A()
C = A
# probe: base.Bool = py.isInstance($a, $C) ^err
# python: isinstance(a, C)
# expect: agree
