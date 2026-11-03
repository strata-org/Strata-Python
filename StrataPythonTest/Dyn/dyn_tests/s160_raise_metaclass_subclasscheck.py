# Test: a raise asks the metaclass's __subclasscheck__, which may make CPython call the class again
class M(type):
    def __subclasscheck__(cls, sub):
        print("check")
        return False
class E(Exception, metaclass=M):
    pass
e = E("x")
try:
    raise e
except Exception as t:
    print(t is e)
