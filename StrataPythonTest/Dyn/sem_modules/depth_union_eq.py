# CPython raises RecursionError from depth 2499 on this path; the rules count at least
# as many C levels and Python frames and stop with a gap before: the small depth
# agrees, the large one stops.
# The rules' check that the arguments are known values follows fewer nested levels than
# CPython's limit, so it stops the large depth first, before the C levels run out.
def mk(d):
    x = int
    for _ in range(d):
        x = list[x] | None
    return x
D = 300
print(mk(D) == mk(D))
D = 2498
print(mk(D) == mk(D))
