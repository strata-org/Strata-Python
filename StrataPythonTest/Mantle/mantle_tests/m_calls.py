# A call evaluates the callee, the positional arguments, then the keyword arguments, as
# CPython does.  Positional arguments are a tuple display.  A lone `*x` is evaluated in place
# but made a tuple by `argsTuple` after the keyword arguments, so `f(*g(), k=h())` calls
# `h()` before iterating `g()`.  Keyword arguments are runs of pairs, and `dictMerge` for
# each `**m`, which rejects a duplicate key naming the callee.
f()
f(a, b)
f(k=a, j=b)
f(a, k=b)
f(*xs)
f(*xs, k=a)
f(a, *xs, b)
f(**m)
f(k=a, **m, j=b, **n)
f(a, *xs, k=b, **m)
f(*xs, **m)
f(k=a, *xs)
