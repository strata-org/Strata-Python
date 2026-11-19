# P3 (dedicated exits) on exception edges.
# setup() and use(x) raise to the same `catch` block: one predecessor is outside the loop.
def a(xs):
    try:
        setup()
        for x in xs:
            use(x)
    except ValueError:
        return -1
    return 0
