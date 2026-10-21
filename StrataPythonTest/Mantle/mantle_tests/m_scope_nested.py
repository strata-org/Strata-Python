# Value-context `and`/`or` and conditional expressions nested in one another, after an
# earlier operand, as values and as conditions.

a = 1
b = 0
c = 2
d = 3


def f(a, b, c, d):
    return a + ((b if c else d) or (c and (d if b else a)))


def g(a, b, c, d):
    return a - (b or c if d else c and d)


def h(a, b, c, d):
    if a + (b or c) and (c if d else b):
        return 1
    return 0


def w(a, b, c):
    while a < (b or c):
        a = a + 1
    return a


def k(a, b, c):
    assert a, a + (b or c)
    return a
