# Test: < on lists and on tuples returns the first differing items' __lt__ result as it is, here a str
class C:
    def __lt__(self, o):
        return "yes"
print([C()] < [C()])
print((C(),) < (C(),))
