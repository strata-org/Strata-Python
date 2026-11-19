# A loop in an `except ... as e` clause: its `break`, its `return`, and the `return` of its
# `else` leave the clause, unbinding `e`.
def f1(xs):
    try:
        g()
    except ValueError as e:
        for x in xs:
            if x:
                break
            if y(x):
                return x
            h(x)
        else:
            return 2
    return 0
