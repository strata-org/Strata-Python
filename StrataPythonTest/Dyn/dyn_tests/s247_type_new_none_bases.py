# Test: type.__new__ with None as bases says None, as CPython's argument errors do
type.__new__(type, "X", None, {})
