# `del`: a name is checked as a read is, but without the builtins fallback, then unassigned.
# Targets are deleted left to right, a tuple or list element by element.
x = 1
del x
del o.a, o[k]
del o[a:b]
del (p, [q, r])
len = 1
del len

def f():
    y = 1
    del y
    return y

def g():
    global z
    del z
