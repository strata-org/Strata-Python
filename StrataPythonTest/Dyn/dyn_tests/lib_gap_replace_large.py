# A replace whose result the model does not hold stops with a gap, where CPython may raise
# MemoryError.
print(len(("a" * 16385).replace("a", "b" * 16384)))
