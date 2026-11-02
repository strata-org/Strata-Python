# Test: a direct call of a class's own __init_subclass__, which is a class method without @classmethod
class Base:
    def __init_subclass__(cls):
        print("isc", cls.__name__)
Base.__init_subclass__()
