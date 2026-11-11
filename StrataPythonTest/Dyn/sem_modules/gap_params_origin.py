# __parameters__ reads __typing_subst__ of a nested alias, which its origin may define.
class L(list):
    __typing_subst__ = 1
print(L[int].__parameters__)
print(list[L[int]].__parameters__)
