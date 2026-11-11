x = 1
u = int | str
# probe: base.Bool = py.isInstance($x, $u) ^err
# python: isinstance(x, u)
# expect: agree
