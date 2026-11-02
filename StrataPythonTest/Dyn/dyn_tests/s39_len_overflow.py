# Test: the truth of an object whose __len__ returns 2 ** 70 raises OverflowError
class C:
    def __len__(self):
        return 2 ** 70
if C():
    print("true")
