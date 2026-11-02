# Test: a property subclass with a __doc__ slot (an instance with slots of a built-in type's subclass gaps)
class slotted_prop(property):
    __slots__ = ("foo", "__doc__")
p = slotted_prop(doc="what's up")
print(p.__doc__)
