# ty:           clean (no diagnostic)
# CPython:      TypeError (can only concatenate str (not "int") to str)
# mypy --strict: error [var-annotated]  (mypy demands an annotation for `d`)
#
# ty unsoundness: an empty dict literal `{}` is inferred as dict[Unknown, Unknown]
# by the embedded ty. `d.get("k", "s")` therefore returns Unknown (ty does not
# even use the "s" default to refine the value type here), so `v + 1` is accepted.
# At runtime the key is absent, `.get` returns the default "s", and `"s" + 1`
# raises TypeError. mypy --strict instead forces an annotation on `d`
# (var-annotated), which would surface the mismatch; ty stays silent.

d = {}
v = d.get("k", "s")
v + 1
