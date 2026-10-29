# `(x := e)` evaluates `e`, writes it to `x`, and produces it, as CPython's `COPY` and
# `STORE`.  In a condition, the produced value is tested.
y = (x := f())
if (n := g()) > 0:
    r = n
while (m := h()):
    r = m
z = [(w := a), w]
def f(g):
    y = (x := g())
    (a := (b := 1))
    return x, y, a, b
def h(g):
    global G
    (G := g())
