# P5 (tail-closed range): the inner loop and the `return` are in the lexical body of the outer
# loop, but cannot reach its latch.
def e(v):
    i = 0
    while g(i):
        if h(i):
            i += 1
            continue
        while k():
            m()
        return v
    return -1
