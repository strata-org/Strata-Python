# A padding wider than the model holds stops with a gap, where CPython may raise MemoryError.
print(len("x".ljust(2 ** 40)))
