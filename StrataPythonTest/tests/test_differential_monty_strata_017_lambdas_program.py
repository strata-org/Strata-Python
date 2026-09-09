# Feature: LAMBDAS  lambda x: ...  (out-of-worklist; sibling of closures, 001).
#
# Monty result (pydantic-monty 0.0.18): IN. Lambdas run — non-capturing,
# capturing (closes over an enclosing var), and as a higher-order argument:
#   inc = lambda x: x+1; k=10; add_k = lambda x: x+k;
#   sorted([3,1,2], key=lambda v: -v)
#   [inc(5), add_k(5), ys]  -> [6, 15, [3, 2, 1]]   (MATCH CPython)
#
# Frontend: OUT (gated, safe). frontend-subset.md:369-371 lists `lambda x: x+1`
# (lambdas anywhere) OUT — "Laurel has no closure model today; nested functions
# with free variables require cell-object modeling." The Layer-2 gate diagram
# (:30) explicitly rejects `lambda`. No `.Lambda` translation in the front end;
# pending test_lambda.py (no accepted lambda test).
#
# Matrix cell: (C) — Monty IN, Frontend OUT, would have to add support.
# A lambda is an anonymous closure, so this is the same gap as closures (001):
#   * non-capturing lambda -> easy (A): desugar to a named pure def.
#   * capturing  lambda    -> needs Laurel cells (shares 001's cell-capture work).
#
# This program is in Monty's subset (lambdas + sorted with key).

inc = lambda x: x + 1
k = 10
add_k = lambda x: x + k          # captures enclosing k (cell capture)
xs = [3, 1, 2]
ys = sorted(xs, key=lambda v: -v)

[inc(5), add_k(5), ys]
