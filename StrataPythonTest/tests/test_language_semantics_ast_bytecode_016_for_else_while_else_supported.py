# else clause for search pattern
def find(lst, target):
    for item in lst:
        if item == target:
            return item
    else:
        return None  # only reached if not found
assert find([1,2,3], 2) == 2
assert find([1,2,3], 9) is None
print("OK: for-else — search pattern works correctly")
