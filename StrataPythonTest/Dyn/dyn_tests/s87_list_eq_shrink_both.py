# Test: == of two lists where an item's __eq__ empties both lists and returns False
class K:
    def __eq__(self, o):
        del a[:]
        del b[:]
        return False
a = [K()]
b = [0]
print(a == b)
