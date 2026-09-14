"""A base must be an admitted class, bound at the class declaration.

Dispatch tables are derived from the declared class graph. A base that names
something which is not an admitted class, or is not bound where the class is
declared, leaves the MRO underdetermined -- and an MRO the analysis guesses is a
dispatch table describing a program that does not exist.
"""


class FromUndeclared(NotAClassAnywhere):
    def m(self) -> int:
        return 1


later = 1


class FromNonClass(later):
    def m(self) -> int:
        return 2
