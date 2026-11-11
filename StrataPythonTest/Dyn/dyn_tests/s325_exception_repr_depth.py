# The repr of an exception nested 8000 deep: CPython runs each built-in __repr__ as the C slot, which
# costs one C level per exception, and so does the model, so the repr fits both limits.
class E(Exception):
    pass
e = E()
for _ in range(8000):
    e = E(e)
print(len(repr(e)))
