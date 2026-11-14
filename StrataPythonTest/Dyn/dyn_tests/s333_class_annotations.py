# A class's __annotations__: its own namespace's entry, made by its annotated names; a built-in
# type has none.
class A:
    x: int
    y: str = "a"
print(A.__annotations__)
print(A.__annotations__ is A.__dict__["__annotations__"])
try:
    int.__annotations__
except AttributeError as e:
    print("AttributeError", e)
