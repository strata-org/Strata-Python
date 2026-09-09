# NAIVE MODEL WOULD GET WRONG: assumes super() is a regular function call
class Base:
    def method(self): return "base"
class Child(Base):
    def method(self):
        # Naive: super() needs explicit args. CPython: __class__ cell injected implicitly
        return super().method()
assert Child().method() == "base"
print("BOUNDARY: naive model can't resolve zero-arg super(); CPython injects __class__ cell")
