# List, set and dict comprehensions are inlined into the enclosing scope; a generator
# expression is its own scope.  Iteration variables do not leak; the outermost iterable is
# evaluated in the enclosing scope.
def f(xs, ys):
    a = [x for x in xs if x]
    b = {x: y for x in xs for y in ys}
    c = {x for x in xs}
    d = (x * k for x in xs)
    k = 2
    return a, b, c, d, x


z = [w for w in range(3)]
nested = [[i * j for j in range(i)] for i in range(4)]
