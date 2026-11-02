# Test: an instance of a user class has __weakref__, which the model doesn't hold
class E:
    pass


print(E().__weakref__)
