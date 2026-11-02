# Test: a class's __doc__ that its body binds to a descriptor is read through the descriptor's __get__
class DocDescr:
    def __get__(self, obj, owner):
        if obj is None:
            return "class " + owner.__name__
        return "instance of " + owner.__name__
class NewClass:
    __doc__ = DocDescr()
print(NewClass.__doc__, NewClass().__doc__)
class A:
    @classmethod
    @property
    def __doc__(cls):
        return "A doc for " + cls.__name__
print(A.__doc__)
class B:
    """First"""
    @classmethod
    @property
    def __doc__(cls):
        return "Second"
print(B.__doc__)
class C:
    """Plain"""
print(C.__doc__, C().__doc__)
