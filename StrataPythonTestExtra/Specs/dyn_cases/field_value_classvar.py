# A class variable reads the class body's namespace as bound so far, then the globals: y reads the
# global class x, and z reads the field's value 0.
class x:
    pass

class C:
    y = x
    x: int = 0
    z = x
