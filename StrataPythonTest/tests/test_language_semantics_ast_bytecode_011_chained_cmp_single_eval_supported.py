# Chained comparison: middle evaluated once
count = [0]
def val():
    count[0] += 1
    return count[0]
assert 0 < val() < 10  # val() returns 1, called once
assert count[0] == 1
print("OK: chained cmp — middle operand evaluated once")
