def f(xs):
    return {x: (yield x) for x in xs}
