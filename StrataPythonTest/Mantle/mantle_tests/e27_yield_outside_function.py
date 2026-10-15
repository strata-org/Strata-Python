# `yield` and `yield from` at module level or in a class body: CPython's compiler rejects
# them, but its symbol table does not.
x = (yield 1)
class C:
    y = yield
    z = yield from w
r = [x for x in (yield 1)]  # a comprehension's outermost iterable is the module's
def f():
    class D:
        v = yield  # a class body inside a function is still not a function
