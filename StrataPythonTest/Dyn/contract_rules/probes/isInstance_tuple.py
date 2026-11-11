x = True
cs = (str, int)
# probe: base.Bool = py.isInstance($x, $cs) ^err
# python: isinstance(x, cs)
# expect: agree
