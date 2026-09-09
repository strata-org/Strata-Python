# Augmented assignment evaluates subscript once
calls = []
def idx():
    calls.append(1)
    return 0
a = [10]
a[idx()] += 5
assert a == [15] and len(calls) == 1
print("OK: augassign single eval — subscript called once")
