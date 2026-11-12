from pyhard import loop_invariant, OLD

class Ctx:
    def __enter__(self):
        return self

    def __exit__(self, *a):
        print("exit")
        return False

def f(n):
    i = 0
    loop_invariant(lambda: i <= n)
    while i < n:
        with Ctx():
            i += 1
            break
    return i

print(f(3))
