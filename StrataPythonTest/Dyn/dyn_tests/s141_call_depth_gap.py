# Test: calls through __call__ count their C level, so deep recursion stops with a gap
def nest_list(n, x):
    a = x
    i = 0
    while i < n:
        a = [a]
        i += 1
    return a
def nest_tuple(n):
    t = ()
    i = 0
    while i < n:
        t = (t,)
        i += 1
    return t
A = nest_list(7000, {nest_tuple(890): 1})
B = nest_list(7000, {nest_tuple(890): 1})
class C:
    def __call__(self, n):
        if n == 0:
            try:
                return A == B
            except RecursionError:
                return "RecursionError"
        return self(n - 1)
print(C()(850))
del A, B
