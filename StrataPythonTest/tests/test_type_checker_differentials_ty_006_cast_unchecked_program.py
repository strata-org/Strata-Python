# ty:           clean (no diagnostic)
# CPython:      TypeError (can only concatenate str (not "int") to str)
# mypy --strict: clean  <-- SHARED blind spot: mypy --strict misses it too
# Monty runtime: ImportError (Monty has no `typing` module) -- see analysis.md
#
# ty unsoundness (explicit escape hatch): `cast(int, "s")` asserts to the checker
# that "s" is an int. ty (like every PEP 484 checker) TRUSTS cast unconditionally
# and types `x` as int, so `x + 1` is accepted. At runtime x is still "s" and
# `"s" + 1` raises TypeError. This is the one case in this corpus where BOTH ty
# AND mypy --strict are silent -- cast is a genuine type-soundness hole shared by
# all PEP 484 checkers, not a ty-specific gap.
#
# Caveat for the embedded-Monty story: Monty's runtime cannot import `typing`, so
# under Monty the program fails earlier with ImportError. The cast hole therefore
# matters mainly for STANDALONE ty (classes/full stdlib); recorded here because it
# is the cleanest pure type-soundness witness and the only shared mypy/ty miss.

from typing import cast

x = cast(int, "s")
x + 1
