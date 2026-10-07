def f(xs):
    return [x for x in (lambda: (y := xs))()]
