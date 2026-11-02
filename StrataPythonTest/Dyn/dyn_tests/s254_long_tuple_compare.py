# Test: == and in on long tuples
a = (0,) * 100000
b = (0,) * 100000
r = a == b
s = 1 in a
