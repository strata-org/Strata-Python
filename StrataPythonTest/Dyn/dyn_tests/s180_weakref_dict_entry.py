# Test: an instance dict entry named __weakref__, which the class's data descriptor hides
class E:
    pass
e = E()
e.__dict__['__weakref__'] = 1
print(e.__weakref__)
