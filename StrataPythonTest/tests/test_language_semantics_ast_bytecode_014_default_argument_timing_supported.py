# Default evaluated once at def-time (mutable default pattern)
def append_to(item, target=[]):
    target.append(item)
    return target
a = append_to(1)
b = append_to(2)
assert a is b  # same list!
assert b == [1, 2]
print("OK: default argument timing — shared mutable default")
