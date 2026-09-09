# PEP 479: StopIteration in generator becomes RuntimeError
def bad_gen():
    next(iter([]))  # raises StopIteration
    yield
try:
    next(bad_gen())
except RuntimeError:
    pass  # correctly wrapped
print("OK: generator StopIteration wrapping — PEP 479")
