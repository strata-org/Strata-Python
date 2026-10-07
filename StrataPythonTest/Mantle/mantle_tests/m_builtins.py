# Builtin names: an unbound builtin, and a global that may shadow one.
n = len("abc")
m = min(1, 2)
if n:
    print = 3
print(m)
