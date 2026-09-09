# ty:           clean (no diagnostic)
# CPython:      TypeError (can only concatenate str (not "int") to str)
# mypy --strict: error [no-untyped-def, no-any-return, no-untyped-call]
#
# ty unsoundness (the strong case): an Unknown value LAUNDERS through a declared
# return annotation. `src()` is Unknown (unannotated). `f` is annotated `-> int`
# and returns `src()`; ty does NOT flag "returning Unknown/Any where int is
# declared" (mypy --strict does, via no-any-return). Downstream, ty trusts the
# `-> int` annotation, so `f() + 1` is accepted as int + int. At runtime `f()`
# yields "s" and `"s" + 1` raises TypeError. ty has the annotation and still
# misses it -- this is exactly why Frontend must `assert` a hint, never `assume` it.

def src():
    return "s"

def f() -> int:
    return src()

f() + 1
