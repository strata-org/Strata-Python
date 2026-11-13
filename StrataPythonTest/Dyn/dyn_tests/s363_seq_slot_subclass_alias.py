# A subclass of list whose __radd__ is list's + slot: CPython calls it reflected, so [1] + L1([2])
# is [2, 1]; the model stops with a gap.
class L1(list):
    __radd__ = list.__add__
print([1] + L1([2]))
