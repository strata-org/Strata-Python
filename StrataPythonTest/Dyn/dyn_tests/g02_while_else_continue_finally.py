# P2 (single latch) and P3 (dedicated exits).
# Three back edges (fall-through, `continue` in an `except` clause, `continue` in `finally`),
# and the `else` clause jumps into the block that `break` also jumps to.
def b(n):
    i = 0
    while i < n:
        try:
            if p(i):
                continue
            work(i)
        except KeyError:
            continue
        finally:
            if q(i):
                continue
        if r(i):
            break
        i += 1
    else:
        log()
    return i
