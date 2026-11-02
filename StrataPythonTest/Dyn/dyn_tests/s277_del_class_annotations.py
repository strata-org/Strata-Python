# Test: deleting the __annotations__ of a class that has none raises CPython's AttributeError
class C:
    pass
del C.__annotations__
