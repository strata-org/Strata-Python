# A subclass of reversed stops with a gap, also where CPython returns a list_reverseiterator.
class R(reversed):
    pass


print("before")
print(type(R([1, 2, 3])).__name__)
