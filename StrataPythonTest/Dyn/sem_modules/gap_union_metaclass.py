# The == of unions hashes and compares their arguments as a set does, which runs a metaclass's
# __hash__ and __eq__.
class M(type):
    def __hash__(cls):
        return 1
    def __eq__(cls, other):
        return isinstance(other, M)
class A(metaclass=M):
    pass
class B(metaclass=M):
    pass
print(A | int)
print((A | int) == (B | int))
