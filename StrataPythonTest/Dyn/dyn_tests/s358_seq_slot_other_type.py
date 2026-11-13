# A list's += slot wrapper (list.__iadd__) set on a class that isn't a list: CPython calls it, and
# its type check raises; the model stops with a gap where it binds the slot.
class C:
    __iadd__ = list.__iadd__
x = C()
try:
    x += 1
    print("ok")
except TypeError as e:
    print("TypeError", e)
