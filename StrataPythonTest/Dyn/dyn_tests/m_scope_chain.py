# Comparison chains of three or more links, and one whose later operand branches.

a = 1
b = 2
c = 3
d = 0
e = 4

r = a < b < c < (d or e)
s = a < b < c < d
t = a < b <= c < d < e


def f(a, b, c, d, e):
    return a < b < c < (d or e)


def g(a, b, c, d):
    if a < b < c < d:
        return 1
    return 0


def h(a, b, c):
    return a + (a < b < c)
