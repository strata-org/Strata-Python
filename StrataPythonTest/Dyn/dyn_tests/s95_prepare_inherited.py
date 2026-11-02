# Test: an inherited __prepare__ gets the class keywords, which object.__init_subclass__ then rejects
class M(type):
    @classmethod
    def __prepare__(mcls, name, bases, **kw):
        print("prepare", name, kw["flag"])
        return {}
class N(M):
    pass
class C(metaclass=N, flag=1):
    pass
