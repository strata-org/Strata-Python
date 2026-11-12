from pyhard import loop_invariant, OLD

def f(xs):
    bad = 0
    loop_invariant(lambda: bad >= 0)
    for x in xs:
        try:
            1 // x
        except ZeroDivisionError:
            bad += 1
    return bad

print(f([1, 0, 0]))
