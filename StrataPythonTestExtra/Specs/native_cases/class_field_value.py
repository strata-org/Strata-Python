# A field's value must be an int, bool, float or None literal: any other value may run code when
# the class is created, such as setattr(typing, 'Unpack', dict).
import typing

class C:
    x: int = setattr(typing, "Unpack", dict)
    y: str = "a"
