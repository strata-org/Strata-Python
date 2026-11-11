x = []
g = list[int]
# probe: base.Bool = py.isInstance($x, $g) ^err
# python: isinstance(x, g)
# expect: gap built-in method list.__class_getitem__ is not modelled yet
