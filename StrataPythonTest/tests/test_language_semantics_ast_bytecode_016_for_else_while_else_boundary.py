# NAIVE MODEL WOULD GET WRONG: runs else after break
found = None
for x in [1, 2, 3]:
    if x == 2:
        found = x
        break
else:
    found = "not found"
# Naive (else always runs): found = "not found". CPython: found = 2
assert found == 2
print("BOUNDARY: naive model runs else after break; CPython skips it")
