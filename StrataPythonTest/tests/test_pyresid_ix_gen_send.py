# Generator three-way arms: next() with default is total, bare next()
# carries the exhaustion category, and send/close are real methods with
# no transfer yet: opaque, havoc, external-havoc obligation, never a
# fabricated AttributeError.
def counter(n: int):
    for i in range(n):
        yield i


g = counter(3)
a = next(g, 0)
b = next(g)
g.close()
z = g.no_such_method()
