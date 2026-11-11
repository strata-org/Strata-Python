class A:
    @property
    def __class__(self):
        raise KeyError("read")
a = A()
T = (A, str)
# probe: base.Bool = py.isInstance($a, $T) ^err
# python: isinstance(a, T)
# expect: agree
