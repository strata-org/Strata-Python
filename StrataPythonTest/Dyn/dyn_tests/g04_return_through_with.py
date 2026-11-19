# P3, P4 and P7: `return` leaves two loops and a `with` at once; `break` leaves only the inner loop.
def d(rows):
    for r in rows:
        with lock():
            for x in r:
                if bad(x):
                    return x
                if skip(x):
                    break
        tidy(r)
    return None
