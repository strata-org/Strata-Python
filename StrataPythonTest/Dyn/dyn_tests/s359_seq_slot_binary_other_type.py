# A list's + slot wrapper (list.__add__) set as __add__ on a class that isn't a list: CPython calls
# it, and its type check raises; the model stops with a gap where it binds the slot.
class D:
    __add__ = list.__add__
try:
    print(D() + [1])
except TypeError as e:
    print("TypeError", e)
