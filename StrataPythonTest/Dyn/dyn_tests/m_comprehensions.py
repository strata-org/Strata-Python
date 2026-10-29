# Comprehensions: a tuple target, two `if`s, two `for` clauses, a dict comprehension (key
# before value), a set comprehension, a lambda capturing the iteration variable (a fresh cell
# per evaluation), and class bodies' comprehensions reading the enclosing function's local,
# also one the class binds too (`free_class`).
def f(pairs, ys):
    a = [x + y for x, y in pairs if x if y]
    b = [(x, y) for x, _ in pairs for y in ys]
    c = {k: v for k, v in pairs}
    d = {y for y in ys}
    e = [lambda: y for y in ys]
    return a, b, c, d, e


def outer(n):
    class C:
        xs = [i * n for i in range(2)]
    return C


def shadowed():
    n = 1

    class D:
        n = 2
        xs = [n for _ in range(1)]
    return D
