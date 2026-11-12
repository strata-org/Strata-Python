from pyhard import loop_invariant, OLD

def f(n):
    log = []
    i = 0
    loop_invariant(lambda: i <= n)
    while i < n:
        try:
            i += 1
            if i == 1:
                continue
        finally:
            log.append(i)
    return log

print(f(3))
