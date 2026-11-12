from pyhard import loop_invariant, OLD

class Ctx:
    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False

def f(n, flag):
    i = 0
    if flag:
        loop_invariant(lambda: i <= n)
        while i < n:
            i += 1
    try:
        loop_invariant(lambda: i >= 0)
        while i > 0:
            i -= 1
    finally:
        pass
    with Ctx():
        loop_invariant(lambda: i <= n)
        while i < n:
            i += 1
    for k in range(1):
        pass
    else:
        loop_invariant(lambda: i == n)
        while i < n:
            i += 1
    return i

print(f(2, True))
