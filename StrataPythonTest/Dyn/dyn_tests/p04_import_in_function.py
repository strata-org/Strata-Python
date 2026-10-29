# An import inside a function binds a local.
def f():
    import math
    from os import sep as s
    return math.pi, s


def g():
    import json

    def h():
        return json.dumps(1)
    return h
