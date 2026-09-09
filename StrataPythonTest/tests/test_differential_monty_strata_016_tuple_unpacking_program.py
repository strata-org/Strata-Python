# Feature: TUPLE UNPACKING / MULTIPLE ASSIGNMENT  a, b = ...  (out-of-worklist).
#
# Result: cell (A) for ordinary unpacking — and another Frontend doc-understatement.
# frontend-subset.md:390-391,518 lists tuple unpacking as OUT/"may grow" ("No tuple
# unpacking a, b = 1, 2 in v1"), but the FRONT END IMPLEMENTS IT via a sound
# eval-once temp desugar (PythonToLaurel.lean:1419-1423:
#   "Tuple unpacking: a, b = rhs  ->  tmp = rhs; a = tmp[0]; b = tmp[1]").
# Accepted (non-pending) tests: test_tuple_unpack.py, test_tuple_swap.py,
# test_var_swap.py, test_multi_assign.py, test_multi_assign_triple.py.
#
# Monty result (pydantic-monty 0.0.18): CPython-faithful on every form.
#   a,b=1,2; a,b=b,a; x,y,z=10,20,30; (p,q),r=(1,2),3  -> [2,1,10,20,30,1,2,3] (MATCH)
#   a, *b = 1,2,3                                       -> [1, [2,3]]           (MATCH)
# CPython 3.14.3 agrees.
#
# Sub-feature cells:
#   * basic / swap / nested / triple unpacking  -> (A)  [doc stale; implemented]
#   * starred unpacking  a, *b = ...             -> (C)  Frontend OUT (*-unpack, :654/696;
#                                                         pending test_star_unpack.py)
#   * chained assignment a = b = c               -> OUT  gated (:390); pending
#                                                         test_multi_assign_side_effect.py
#
#   * swap/unpack THROUGH aliases                -> (B)  inherits 005 (value-copy);
#                                                         pending test_soundness_list_swap_via_alias.py
#
# This program is in both subsets (basic + swap + nested unpacking, no aliasing).

a, b = 1, 2
a, b = b, a            # swap: rhs tuple built before any store -> a=2, b=1
x, y, z = 10, 20, 30   # triple
(p, q), r = (1, 2), 3  # nested

[a, b, x, y, z, p, q, r]
