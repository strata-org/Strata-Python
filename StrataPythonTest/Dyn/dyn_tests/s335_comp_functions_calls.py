# The comprehensions in functions of the corpus programs that only define them (m_comprehensions,
# p40, p43, p45, p46, p48, p49, p50), called: an iteration variable named like a local, a lambda
# that captures a comprehension's variable, a class body's comprehension (a free name, a class
# name, __class__ and super()), a walrus that binds a function's, a nonlocal or a global name, and
# a free name read through nested comprehensions.
def show(label, f):
    try:
        print(label, f())
    except Exception as e:
        print(label, type(e).__name__, e)


def p43_free(rows):
    scale = 3

    class C:
        a = [r * scale for r in rows]
    return C.a


def p43_class_name(rows):
    class C:
        k = 1
        a = [r + k for r in rows]
    return C.a


def p43_lambdas(rows):
    class C:
        fs = [lambda: r for r in rows]
    return [f() for f in C.fs]


def p43_class_cell(rows):
    class C:
        own = [__class__ for _ in rows]
    return C.own


def p43_super(rows):
    class C:
        def m(self):
            return [super() for _ in rows]
    return len(C().m())


def m_f(pairs, ys):
    a = [x + y for x, y in pairs if x if y]
    b = [(x, y) for x, _ in pairs for y in ys]
    c = {k: v for k, v in pairs}
    d = {y for y in ys}
    e = [lambda: y for y in ys]
    return a, b, c, d, [g() for g in e]


def m_outer(n):
    class C:
        xs = [i * n for i in range(2)]
    return C


def m_shadowed():
    n = 1

    class D:
        n = 2
        xs = [n for _ in range(1)]
    return D


def p40_f(xs):
    x = 0
    a = [x for x in xs]
    return a, x


def p40_g(xs):
    b = [y * 2 for y in xs]
    y = 1
    return b, y


def p45_f(xs):
    a = [(last := x) for x in xs]
    return a, last


def p45_g(rows):
    a = [[(cell := c) for c in row if c] for row in rows]
    return a, cell


def p45_h(xs):
    total = 0

    def add():
        nonlocal total
        return [(total := total + x) for x in xs]

    return add


def p46_f(xs):
    return [g() for g in [lambda: x for x in xs]]


def p46_g(xs):
    x = 0
    fs = [lambda: x for x in xs]
    return [g() for g in fs], x


def p46_h(xs, ys):
    return [g() for g in [lambda: (x, y) for x in xs for y in ys]]


def p46_k(xs):
    return [g() for g in [lambda y=x: y for x in xs]]


class A:
    def m(self, i):
        return i


class B(A):
    def m(self, rows):
        return [[super().m(i) for i in r] for r in rows]


def p50_f(k, a):
    return [[[k for _ in c] for c in b] for b in a]


def p48_m(xs):
    global g
    return [(g := x) for x in xs]


k48 = lambda xs: ([(y := x) for x in xs], y)

show("p43 free", lambda: p43_free([1, 2]))
show("p43 class name", lambda: p43_class_name([1]))
show("p43 lambdas", lambda: p43_lambdas([1, 2]))
show("p43 class cell", lambda: p43_class_cell([1]))
show("p43 super", lambda: p43_super([1, 2]))
show("m_f", lambda: m_f([(1, 2), (0, 3)], [4, 5]))
show("m_outer", lambda: m_outer(5).xs)
show("m_shadowed", lambda: m_shadowed().xs)
show("p40_f", lambda: p40_f([1, 2]))
show("p40_g", lambda: p40_g([1, 2]))
show("p45_f", lambda: p45_f([1, 2]))
show("p45_g", lambda: p45_g([[1, 0], [2]]))
show("p45_h", lambda: p45_h([1, 2, 3])())
show("p46_f", lambda: p46_f([1, 2]))
show("p46_g", lambda: p46_g([1, 2]))
show("p46_h", lambda: p46_h([1, 2], [3]))
show("p46_k", lambda: p46_k([1, 2]))
show("p49", lambda: B().m([[1, 2], [3]]))
show("p50", lambda: p50_f(7, [[[0], [0, 0]], [[0]]]))
show("p48_m", lambda: (p48_m([1, 2]), g))
show("p48_k", lambda: k48([3, 4]))
