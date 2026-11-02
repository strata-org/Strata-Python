# Test: the message of object.__init_subclass__ with a keyword names the class by its qualified name
class Outer:
    class C(x=1):
        pass
