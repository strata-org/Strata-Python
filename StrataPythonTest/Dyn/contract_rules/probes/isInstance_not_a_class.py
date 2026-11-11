x = 1
c = 5
# probe: base.Bool = py.isInstance($x, $c) ^err
# python: isinstance(x, c)
# expect: agree
