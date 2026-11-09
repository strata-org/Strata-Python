# Test: the truth of a range longer than a C ssize_t, by bool() and by __bool__
r = range(2 ** 70)
print(r.__bool__(), range(0).__bool__())
if r:
    print("truthy")
