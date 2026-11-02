# Test: __prepare__ is read with the attribute protocol, so a metaclass's metaclass gives it
class MM(type):
    def __prepare__(cls, name, bases):
        print("MM prepare", name)
        return {}
class M(type, metaclass=MM):
    pass
class X(metaclass=M):
    pass
