# Literals, operators, `not`, unary minus, and a chained comparison.
def exprs(a, b, c):
    s = "s"
    by = b"\x00\xff"
    e = ...
    t = (a + b - c * 2 / 3 // 4 % 5) ** 2
    u = not -a
    return a < b <= c
