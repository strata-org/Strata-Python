from typing import TypedDict
try:
    class A(TypedDict):
        __annotations__ = 5
    print("made")
except Exception as e:
    print(type(e).__name__, e)
