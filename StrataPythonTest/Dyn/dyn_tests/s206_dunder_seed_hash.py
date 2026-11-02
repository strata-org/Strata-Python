# Test: number dunders of int and float on an int whose number depends on the hash seed
h = "a".__hash__()
r = (1).__add__(h)
print(r is NotImplemented)
print((2.0).__mul__(h) is NotImplemented)
