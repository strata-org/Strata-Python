# NAIVE MODEL WOULD GET WRONG: evaluates default at each call
call_count = [0]
def make_default():
    call_count[0] += 1
    return []
def f(x=make_default()):
    x.append(1)
    return x
f(); f(); f()
# Naive (eval at call time): make_default called 3 times, each call gets fresh list
# CPython: called once at def-time, same list reused
assert call_count[0] == 1
print("BOUNDARY: naive model calls default factory each time; CPython calls it once")
