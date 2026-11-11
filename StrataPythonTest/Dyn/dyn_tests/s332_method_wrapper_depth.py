# A method-wrapper in a class's namespace, such as x.__repr__, is not a slot wrapper, so CPython runs
# the class's __repr__ through slot_tp_repr, and the call of the method-wrapper costs a C level:
# 6000 nested such reprs run past CPython 3.12's C recursion limit, which raises RecursionError.
# The model must count that call and stop with a gap.
x = ()
for i in range(6000):
    class C:
        __repr__ = x.__repr__
    x = (C(),)
print(len(repr(x)))
