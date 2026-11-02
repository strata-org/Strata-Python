# Test: __set_name__ runs for each class attribute in order, before the base's __init_subclass__
log = []
class D:
    def __set_name__(self, owner, name):
        print("set_name", name)
class Base:
    def __init_subclass__(cls, **kw):
        print("isc", cls.__name__)
class C(Base):
    a = D()
    b = D()
