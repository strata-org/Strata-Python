# An operand evaluated before a value-context `and`/`or` is used after it.

a = 1
b = 0
c = 2

x = a + (b or c)
y = [a, b and c]


def f(a, b, c):
    return a + (b or c)


def g(a, b, c):
    return a * (b and c or a)
