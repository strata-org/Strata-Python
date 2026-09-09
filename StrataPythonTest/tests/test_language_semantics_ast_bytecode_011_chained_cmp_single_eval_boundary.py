# NAIVE MODEL WOULD GET WRONG: desugars a < b() < c as (a < b()) and (b() < c)
counter = [0]
def b():
    counter[0] += 1
    return counter[0]
result = 0 < b() < 10
# Naive desugaring: b() called twice → returns 1 then 2
# CPython: b() called once → returns 1, reused for both comparisons
assert counter[0] == 1
assert result == True
print("BOUNDARY: naive desugaring calls b() twice; CPython calls it once")
