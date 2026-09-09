# Feature: OBJECT IDENTITY — `id()` / `is` (worklist item 4).
#
# Monty result (pydantic-monty 0.0.18, the running oracle):
#   [True, True, False, True]
#     x is None              -> True   (None-check: matches CPython)
#     id(a) == id(b) (alias) -> True   (Monty models reference identity)
#     id(a) == id(c) (dist.) -> False  (distinct objects distinguished)
#     int("1000") is int("1000") -> True   <-- DIVERGES from CPython
# CPython 3.14.3:
#   [True, True, False, False]   (int identity: separately-built 1000s are NOT the same object)
#
# Strata front end:
#   - `is None` / `is not None`: TRANSLATED soundly. None is a singleton in the
#     Any value model, so identity == equality (PythonToLaurel.lean:628-631).
#   - `is` on a non-None RHS, and `id(x)`: REJECTED at the gate
#     (PythonToLaurel.lean:644/647: unsupportedConstruct "`is` is only supported
#     with None"); `id` needs a heap model Frontend does not have
#     (frontend-subset.md:493-496). Pending: test_is_non_none.py, test_int_identity.py.
#
# Matrix: the feature SPLITS.
#   * `is None` / `is not None`  -> cell (A): Monty IN, Frontend VERIFIABLE. Sweet spot.
#   * `id()` + `is` on non-None  -> cell (C): Monty IN (models identity), Frontend OUT
#     (rejected, needs a heap/Composite model). Adding it also inherits Monty's
#     int over-interning divergence -> a sound encoding must pick an oracle.
#
# This program is in Monty's subset (None, list/int builtins; no classes).

x = None
a = [1, 2]
b = a              # alias of a
c = [1, 2]         # distinct list, equal value

# Observable tuple: [ (A) None-check, (C) alias id, (C) distinct id,
#                     (C/divergent) int identity ]
[x is None, id(a) == id(b), id(a) == id(c), int("1000") is int("1000")]
