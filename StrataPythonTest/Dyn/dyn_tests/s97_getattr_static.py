# Test: a __getattr__ that is a staticmethod gets only the attribute name
class C:
    @staticmethod
    def __getattr__(name):
        return name == "abc"
print(C().abc)
