from typing import TypedDict
try:
    class A(TypedDict):
        __annotations__ = {1: int}
    print("made", A.__required_keys__ == {1})
except Exception as e:
    print(type(e).__name__, e)
