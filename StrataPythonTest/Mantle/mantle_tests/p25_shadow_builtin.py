# Module and local bindings shadow builtins.
def len(x):
    return 0


def f(xs):
    list = [1]
    return len(xs), list, max(xs)
