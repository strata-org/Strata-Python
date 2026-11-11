from typing import TypedDict
class A(TypedDict):
    x: int
A.__required_keys__ = ["x", "y"]
try:
    class B(A):
        z: int
    print("made", B.__required_keys__ == {"x", "y", "z"})
except TypeError as e:
    print("TypeError:", e)
