# ty:           clean (no diagnostic)
# CPython:      TypeError (can only concatenate str (not "int") to str)
# mypy --strict: error [no-untyped-def, no-untyped-call]
#
# ty unsoundness (dual of 003, at the argument boundary): an Unknown value passes
# into a declared `int` parameter unchecked. `src()` is Unknown; `use(src())`
# binds it to `n: int`. ty does not flag the Unknown -> int argument, and `use`'s
# body `n + 1` is fine for the declared int. At runtime n is "s" -> TypeError.
# The wrong-typed value crosses the annotated boundary that ty trusts.

def src():
    return "s"

def use(n: int) -> int:
    return n + 1

use(src())
