# A closure three levels deep: `a` passes through `g` and `h`; `b` through `h`.
def f():
    a = 1

    def g():
        b = 2

        def h():
            def k():
                return a + b
            return k
        return h
    return g
