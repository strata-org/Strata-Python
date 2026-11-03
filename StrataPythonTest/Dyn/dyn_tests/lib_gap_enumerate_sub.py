# A subclass of enumerate stops with a gap.
class E(enumerate):
    pass


print("before")
print(type(E("ab")).__name__)
