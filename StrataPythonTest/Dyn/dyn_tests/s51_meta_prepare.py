# Test: a metaclass's __prepare__ gives the namespace that the class body starts from
class M(type):
    @classmethod
    def __prepare__(mcls, name, bases):
        print("prepare", name)
        return {"x": 1}
class C(metaclass=M):
    pass
print(C.x)
