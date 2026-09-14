"""`unbound-base`: a base named before it is bound.

CPython raises `NameError` at the `class A` statement, so there is no program to
analyse. Distinct from `unsupported-base`, which is a base that resolves to
something the model has no class for.
"""


class A(B):
    pass


class B:
    pass
