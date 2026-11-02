# Test: a function assigned to a base's __init_subclass__ after its class statement is called without cls
class Base:
    pass
Base.__init_subclass__ = lambda: print("no cls")
class D(Base):
    pass
print("made")
