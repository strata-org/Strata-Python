# Test: a write of a class's read-only __basicsize__ raises AttributeError
class C:
    pass
C.__basicsize__ = 5
print("after")
