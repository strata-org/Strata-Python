# CPython raises RecursionError from depth 4998 on this path; the rules count at least
# as many C levels and Python frames and stop with a gap before: the small depth
# agrees, the large one stops.
def mk(d):
    x = int
    for _ in range(d):
        x = list[x]
    return x
D = 1000
print(mk(D) == mk(D))
D = 4997
print(mk(D) == mk(D))
