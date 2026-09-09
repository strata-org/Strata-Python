def variadic(*args, **kwargs):
    return args


xs = [1, 2, 3]
a, *rest = xs
merged = {**{"a": 1}}
