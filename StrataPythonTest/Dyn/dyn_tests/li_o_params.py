from pyhard import loop_invariant, OLD

def f(a, /, b, c=2, *rest, d, e=[], **kw):
    i = 0
    b = b + 100
    loop_invariant(lambda: OLD(a) == a and OLD(b) + 100 == b and OLD(c) == 2)
    loop_invariant(lambda: len(OLD(rest)) == len(rest) and OLD(d) == d)
    loop_invariant(lambda: len(OLD(e)) == len(e) and len(OLD(kw)) == len(kw))
    while i < 2:
        i += 1
    return i

print(f(1, 2, 3, 4, d=5, x=6))
