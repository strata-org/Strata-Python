# Test: type.__new__ of a class that is not a subtype of type
t = type.__new__(int, 'N', (), {'__module__': 'm'})
