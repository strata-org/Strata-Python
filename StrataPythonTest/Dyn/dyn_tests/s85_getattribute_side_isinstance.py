# Test: isinstance reads the object's __class__ once, through its class's __getattribute__
n = 0
class B:
    def __getattribute__(self, name):
        global n
        n = n + 1
        return object.__getattribute__(self, name)
print(isinstance(B(), int), n)
