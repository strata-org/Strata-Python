x = 1
u = int | str
# probe: base.Bool = py.isInstance($x, $u) ^err
# python: isinstance(x, u)
# expect: gap built-in method type.__or__ is not modelled yet
