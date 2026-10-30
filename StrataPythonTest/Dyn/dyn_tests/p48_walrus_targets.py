# A walrus in a comprehension binds in the scope that encloses the comprehension: the lambda
# here, and the global that the function declares there.
k = lambda xs: ([(y := x) for x in xs], y)


def m(xs):
    global g
    return [(g := x) for x in xs]
