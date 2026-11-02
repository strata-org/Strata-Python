# Test: the dunders of int, bool and float called directly
print((1).__add__(2), (1).__add__(1.5) is NotImplemented, (1.5).__add__(1), int.__add__(True, 2))
print((1).__eq__(1.0) is NotImplemented, (1.0).__eq__(1), (2).__lt__(3), (1).__lt__("a") is NotImplemented)
print((3).__neg__(), True.__and__(False), True.__and__(1), (2).__rpow__(3), (2).__truediv__(4))
print((5).__bool__(), (0.0).__bool__(), (7).__index__(), True.__index__(), (5).__rsub__(1))
print((5).__invert__(), (2.5).__neg__(), float.__radd__(1.5, 2))
int.__add__("a", 1)
