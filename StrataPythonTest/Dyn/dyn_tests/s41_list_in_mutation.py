# Test: in on a list where an item's __eq__ empties the list
class K:
    def __eq__(self, o):
        del lst[:]
        return False
lst = [K(), 1, 2]
print(2 in lst)
