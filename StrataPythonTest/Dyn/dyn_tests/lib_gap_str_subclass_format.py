# A str subclass formatted with a spec stops with a gap: CPython 3.12 gives the object itself,
# and its own __str__ runs.
class S(str):
    def __str__(self):
        return "STR"


x = S("abc")
print(f"{x:s}", type(x % ()).__name__)
