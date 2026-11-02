# Test: += on a list with a user object that has only __iter__ extends the list
class Y:
    def __iter__(self):
        return iter([1, 2])
a = [0]
a += Y()
print(a[2])
