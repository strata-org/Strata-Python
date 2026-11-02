# Test: == of two lists where an item's __eq__ empties the other list and returns True
class K:
    def __eq__(self, o):
        del b[:]
        return True
a = [K(), 1]
b = [0, 1]
print(a == b)
