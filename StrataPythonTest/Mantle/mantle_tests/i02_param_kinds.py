# Callee-side binding for every parameter kind.
def pos(x, y):
    print(x, y)
pos(1, 2)
pos(y=2, x=1)
pos(1, y=2)

def rest(x, *more):
    print(x, more)
rest(1)
rest(1, 2, 3)

def kw(x, **opts):
    print(x, opts)
kw(1)
kw(1, a=2, b=3)
kw(x=1, a=2)

def both(first, *more, **opts):
    print(first, more, opts)
both(1, 2, 3, k=4)

def kwonly(a, *, k):
    print(a, k)
kwonly(1, k=2)
kwonly(a=1, k=2)

def posonly(a, /, b):
    print(a, b)
posonly(1, 2)
posonly(1, b=2)

# A keyword matching a positional-only parameter lands in **opts instead.
def absorb(a, /, **opts):
    print(a, opts)
absorb(1, a=2)
