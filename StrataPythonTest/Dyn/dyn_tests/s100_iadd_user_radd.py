# Test: += on a list with an object that has __radd__ uses __radd__ before the list's in-place concatenation
class Y:
    def __radd__(self, o):
        return "radd"
a = [0]
b = a
a += Y()
print(a, b == [0])
