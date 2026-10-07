# A local read before its assignment: UnboundLocalError, even with a global `y`.
y = 0

def with_global():
    z = y
    y = 1
    return z

def without_global():
    w = v
    v = 1
    return w
