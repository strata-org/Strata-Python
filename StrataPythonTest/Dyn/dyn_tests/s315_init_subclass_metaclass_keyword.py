# Test: a class keyword that both the metaclass's __init__ and __init_subclass__ receive
class Base:
    def __init_subclass__(cls, flag):
        print("isc", flag)
class M(type):
    def __init__(cls, name, bases, ns, flag=None):
        print("init", flag)
class A(Base, metaclass=M, flag=1):
    pass
