# Test: a program that defines its own loop_invariant, without importing pyhard, calls it as an
# ordinary function, and the differential test shows that global as a function, not as a marker.
def loop_invariant(p):
    print("called")


def f(n):
    i = 0
    loop_invariant(lambda: i <= n)
    while i < n:
        i += 1
    return i

print(f(2))
