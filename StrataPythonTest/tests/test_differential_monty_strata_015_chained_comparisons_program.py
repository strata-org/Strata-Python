# Feature: CHAINED COMPARISONS  a < b < c  (out-of-worklist).
#
# Result: cell (A) sweet spot. Frontend's own subset doc lists chained comparisons
# as OUT / "may grow" (frontend-subset.md:505-508, 521; negative example line 643/686),
# but the FRONT END ACTUALLY IMPLEMENTS THEM, including Python's evaluate-once
# semantics. The doc lags the implementation.
#
# Monty result (pydantic-monty 0.0.18): CPython-faithful.
#   x=5; [0<x<10, 0<x<3, 1<2<3<4]      -> [True, False, True]   (MATCH)
#   1 < f() < 10  (f appends to a list) -> f called ONCE          (MATCH, eval-once)
# CPython 3.14.3 agrees.
#
# Frontend handling (PythonToLaurel.lean:620-690, .Compare with n>1):
#   - desugars a<b<c to (a<b) and (b<c),
#   - introduces temp variables for intermediate operands that are NOT simple
#     names/literals (Subscript/Attribute/calls are "non-simple"), preserving
#     evaluate-once for side-effecting middles (lines 648-674).
#   Accepted (non-pending) tests: test_chained_compare.py, _triple, _mixed, _verify.
#   The ONE pending test (test_chained_compare_eval_once.py) is blocked by `global`
#   + proc-calls-in-functions (findings 007 / inter-proc), NOT by the comparison.
#
# This program is in both subsets (side-effect-free range checks). It runs on
# Monty/CPython and the Strata front end translates+verifies it.

def in_range(x: int, lo: int, hi: int) -> bool:
    return lo <= x <= hi

def is_sorted_triple(a: int, b: int, c: int) -> bool:
    return a < b < c

# Observable: [range hit, range miss, triple ordered, triple unordered]
[in_range(5, 0, 10), in_range(20, 0, 10), is_sorted_triple(1, 2, 3), is_sorted_triple(3, 2, 1)]
