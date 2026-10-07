def f(xs):
    return [i for i in xs if (j := i) for j in xs]
