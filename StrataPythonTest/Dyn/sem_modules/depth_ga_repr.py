# CPython raises RecursionError from depth 9995 on this path; the rules count at least
# as many C levels and Python frames and stop with a gap before: the small depth
# agrees, the large one stops.
def mk(d):
    x = int
    for _ in range(d):
        x = list[x]
    return x
D = 1000
print(len(repr(mk(D))))
D = 9994
print(len(repr(mk(D))))
