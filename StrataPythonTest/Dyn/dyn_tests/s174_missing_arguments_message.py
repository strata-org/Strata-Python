# Test: a program that reads the message of a call that misses two required positional arguments
# (CPython's message names both)
def f(a, b):
    return a
msg = ""
try:
    f()
except TypeError as e:
    msg = e.args[0]
print(msg)
