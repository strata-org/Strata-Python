class A:
    @property
    def __class__(self):
        return int
x = A()
I = int
# probe: base.Bool = py.isInstance($x, $I) ^err
# python: isinstance(x, I)
# expect: agree
