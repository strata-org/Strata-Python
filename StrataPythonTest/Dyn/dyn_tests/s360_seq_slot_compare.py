# A list's + slot wrapper set as __eq__ on a class that isn't a list: CPython calls it for ==, and
# its type check raises; the model stops with a gap where it binds the slot.
class K:
    __eq__ = list.__add__
try:
    print(K() == 1)
except TypeError as e:
    print("TypeError", e)
