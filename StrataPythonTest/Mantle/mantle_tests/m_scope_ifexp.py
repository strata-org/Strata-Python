# An operand evaluated before a value-context `x if c else y` is used after it.

a = 1
c = True
p = 2
q = 3

y = a + (p if c else q)


def f(a, c, p, q):
    return [a, p if c else q]
