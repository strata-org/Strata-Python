# Locals carried through nested loops with `break` and `continue`, and through a `try`/`finally`
# whose paths rejoin.
def f(xs, ys):
    total = 0
    count = 0
    for x in xs:
        if x < 0:
            continue
        for y in ys:
            if y == x:
                break
            total = total + y
        count = count + 1
    return total, count


def g(n):
    i = 0
    s = 0
    while i < n:
        try:
            s = s + h(i)
        finally:
            i = i + 1
    return s
