# Exception type not evaluated if handler not reached
evaluated = []
def LazyExc():
    evaluated.append(1)
    return ValueError
try:
    pass  # no exception
except LazyExc():
    pass
assert evaluated == []  # LazyExc() never called
print("OK: exception type lazy eval — not called if not needed")
