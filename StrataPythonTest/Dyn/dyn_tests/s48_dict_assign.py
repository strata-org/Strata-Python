# Test: a read of an attribute after a new dict is assigned to the instance's __dict__
class C:
    pass
c = C()
c.__dict__ = {"a": 1}
print(c.a)
