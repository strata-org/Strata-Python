# `for` loops.  Only `next` raises to `stop`, which ends the loop on `StopIteration` and
# passes any other exception on.  `break` skips `else`, and `continue` goes back to `next`.
for x in xs:
    f(x)

for x in xs:
    if p(x):
        break
    if q(x):
        continue
    f(x)
else:
    g()

for a, (b, *c) in xs:
    f(a, b, c)

for o.a in xs:
    pass

for x in xs:
    for y in ys:
        break
    else:
        continue
    break

def first(xs):
    for x in xs:
        return x
    return None
