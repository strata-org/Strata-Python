# CPython raises RecursionError from depth 4998 on this path; the rules count at least
# as many C levels and stop with a gap before: the small depth agrees, the large one
# stops.
def mk(d):
    x = int
    for _ in range(d):
        x = list[x] | None
    return x
D = 1000
print(len(repr(mk(D))))
D = 4997
print(len(repr(mk(D))))
