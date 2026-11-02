# Test: a write of __annotations__ on a class whose metaclass is type
class C:
    pass
C.__annotations__ = {"x": 1}
print(C.__dict__ is not None)
