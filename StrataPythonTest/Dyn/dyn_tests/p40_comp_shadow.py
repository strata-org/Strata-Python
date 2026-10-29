# An iteration variable named like a local of the enclosing function is isolated from it:
# the local keeps its value before and after the comprehension.
def f(xs):
    x = 0
    a = [x for x in xs]
    return a, x


def g(xs):
    b = [y * 2 for y in xs]
    y = 1
    return b, y


x = "module"
c = [x for x in range(3)]
