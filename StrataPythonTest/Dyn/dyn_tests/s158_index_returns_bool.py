# Test: an __index__ that returns a bool warns, and the warning registers itself
class I:
    def __index__(self):
        return True


print([10, 20][I()])
print("__warningregistry__" in globals())
