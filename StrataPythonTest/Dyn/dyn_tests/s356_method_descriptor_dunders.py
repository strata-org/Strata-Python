# A special method that is a method descriptor of another type (int.bit_length): CPython calls it
# unbound, so the descriptor's own check raises its TypeError at each place that looks it up,
# rather than the place treating the dunder as missing.
class A:
    __iter__ = int.bit_length
class B:
    __eq__ = int.bit_length
class C:
    __hash__ = int.bit_length
for f in [lambda: iter(A()), lambda: B() == 1, lambda: {C(): 1}]:
    try:
        print(f())
    except TypeError as e:
        print("TypeError", e)
