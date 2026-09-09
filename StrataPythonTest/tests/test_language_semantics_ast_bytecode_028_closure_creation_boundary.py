# NAIVE MODEL WOULD GET WRONG: assumes closure is a value snapshot
def make():
    x = 1
    def get(): return x
    def set(v): nonlocal x; x = v
    return get, set
get, set = make()
assert get() == 1
set(99)
# Naive (snapshot): get() still returns 1. CPython (shared cell): returns 99
assert get() == 99
print("BOUNDARY: naive snapshot model gives 1; CPython shared cell gives 99")
