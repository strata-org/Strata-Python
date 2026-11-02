# Test: the truth of an object whose __len__ returns an object with __index__ uses that __index__
class I:
    def __index__(self):
        return 0
class C:
    def __len__(self):
        return I()
if C():
    print("true")
else:
    print("false")
