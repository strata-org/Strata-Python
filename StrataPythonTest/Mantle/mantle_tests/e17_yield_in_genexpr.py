def f(xs):
    return list((yield x) for x in xs)
